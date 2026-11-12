-- EPUB -> KEPUB conversion, in pure Lua.
--
-- A KEPUB is an EPUB that Kobo's own reader understands better: every run of text is wrapped
-- in <span class="koboSpan" id="kobo.<paragraph>.<segment>">, which is what the firmware uses for
-- reading position, highlights, dictionary lookups and reading statistics, and the body content
-- is wrapped in the two <div>s Kobo's stylesheet hooks into. The file is called "*.kepub.epub".
--
-- This mirrors what kepubify does for the parts that matter, without needing a binary on the
-- device. The only thing it relies on from KOReader is ffi/archiver (libarchive) for the zip
-- container, which is injectable so the conversion can be exercised outside KOReader.
--
-- Everything is best effort and non-destructive: convertFile writes to a sibling temp file and
-- only replaces/removes anything once the whole new archive is written.

local Kepub = {}

local KEPUB_SUFFIX = ".kepub.epub"

-- Elements whose open/close tags start a new "paragraph" in the koboSpan numbering.
local BLOCK_TAGS = {}
for tag in ([[address article aside blockquote body caption dd details div dl dt fieldset
    figcaption figure footer form h1 h2 h3 h4 h5 h6 header hr li main nav ol p pre section
    summary table tbody td tfoot th thead tr ul]]):gmatch("%a%w*") do
    BLOCK_TAGS[tag] = true
end

-- Content inside these is never wrapped.
local SKIP_TAGS = { script = true, style = true, svg = true, math = true, textarea = true,
                    head = true, title = true }

-- Words that end in a full stop without ending the sentence.
local ABBREVIATIONS = {}
for word in ([[mr mrs ms dr prof sr jr st vs etc fig no vol p pp ch cf al inc ltd co gen col
    capt lt sgt rev hon mt ft sig sigg dott avv ing]]):gmatch("%a+") do
    ABBREVIATIONS[word] = true
end

local MULTIBYTE_CLOSERS = {
    "\226\128\157", -- ” right double quotation mark
    "\226\128\153", -- ’ right single quotation mark
    "\194\187",     -- » right-pointing double angle quotation mark
}

-- Splits text (no leading/trailing whitespace) into sentences. Each returned item is
-- { text = "...", gap = "<whitespace that followed it>" }. Concatenating text..gap over all of
-- them gives back the input exactly -- spans must never change the book's text.
local function splitSentences(text)
    local sentences = {}
    local start = 1
    local i = 1
    local len = #text
    while i <= len do
        local p_start, p_end = text:find("[%.!%?]+", i)
        if not p_start then break end
        local j = p_end + 1
        -- Closing quotes and brackets belong to the sentence they close.
        while j <= len do
            local c = text:sub(j, j)
            if c:match("[%)%]\"']") then
                j = j + 1
            else
                local matched
                for _, mb in ipairs(MULTIBYTE_CLOSERS) do
                    if text:sub(j, j + #mb - 1) == mb then
                        j = j + #mb
                        matched = true
                        break
                    end
                end
                if not matched then break end
            end
        end
        local ws_start, ws_end = text:find("^%s+", j)
        local split = false
        if ws_start then
            split = true
            local after = text:sub(ws_end + 1, ws_end + 1)
            if after == "" then
                split = false -- trailing whitespace is handled by the caller
            elseif after:match("%l") then
                split = false -- "e.g. foo", "approx. three": a sentence starts upper-case
            elseif text:sub(p_start, p_end) == "." then
                local word = text:sub(start, p_start - 1):match("(%a+)$")
                if word and (#word == 1 or ABBREVIATIONS[word:lower()]) then
                    split = false
                end
            end
        end
        if split then
            sentences[#sentences + 1] = {
                text = text:sub(start, j - 1),
                gap = text:sub(ws_start, ws_end),
            }
            start = ws_end + 1
            i = start
        else
            i = j
        end
    end
    if start <= len then
        sentences[#sentences + 1] = { text = text:sub(start), gap = "" }
    end
    return sentences
end

-- Index of the '>' that closes the tag opening at `lt`, skipping over quoted attribute values.
local function findTagEnd(src, lt)
    local i = lt + 1
    while true do
        local pos = src:find("[>\"']", i)
        if not pos then return nil end
        local c = src:sub(pos, pos)
        if c == ">" then return pos end
        local close = src:find(c, pos + 1, true)
        if not close then return nil end
        i = close + 1
    end
end

-- Wraps the text of one XHTML document. Returns the new document, or nil plus a reason when the
-- document should be left as it is.
function Kepub.convertXhtml(src)
    if type(src) ~= "string" or src == "" then
        return nil, "empty document"
    end
    if src:find("koboSpan", 1, true) then
        return nil, "already has koboSpans"
    end

    local out, n = {}, 0
    local function push(s)
        n = n + 1
        out[n] = s
    end

    local pos, len = 1, #src
    local in_body = false
    local saw_body = false
    local skip_name, skip_depth = nil, 0
    local para, seg = 0, 0
    local new_para = true

    local function emitText(text)
        if not in_body or skip_name or not text:find("%S") then
            push(text)
            return
        end
        local lead = text:match("^%s*")
        local trail = text:match("%s*$")
        local core = text:sub(#lead + 1, #text - #trail)
        push(lead)
        for _, s in ipairs(splitSentences(core)) do
            if new_para then
                para = para + 1
                seg = 0
                new_para = false
            end
            seg = seg + 1
            push(string.format('<span class="koboSpan" id="kobo.%d.%d">', para, seg))
            push(s.text)
            push("</span>")
            push(s.gap)
        end
        push(trail)
    end

    while pos <= len do
        local lt = src:find("<", pos, true)
        if not lt then
            emitText(src:sub(pos))
            break
        end
        if lt > pos then
            emitText(src:sub(pos, lt - 1))
        end

        local stop
        -- Comments, CDATA, processing instructions and the doctype pass through untouched.
        local passthrough = true
        if src:sub(lt, lt + 3) == "<!--" then
            local _, e = src:find("-->", lt + 4, true)
            stop = e or len
        elseif src:sub(lt, lt + 8) == "<![CDATA[" then
            local _, e = src:find("]]>", lt + 9, true)
            stop = e or len
        elseif src:sub(lt, lt + 1) == "<?" then
            local _, e = src:find("?>", lt + 2, true)
            stop = e or len
        elseif src:sub(lt, lt + 1) == "<!" then
            stop = src:find(">", lt + 2, true) or len
        else
            passthrough = false
            stop = findTagEnd(src, lt)
            if not stop then
                -- Not well-formed enough to touch safely.
                return nil, "unterminated tag"
            end
            local raw = src:sub(lt, stop)
            local closing = raw:sub(2, 2) == "/"
            local name = raw:match("^</?([%w_:%-%.]+)")
            local self_closing = raw:sub(-2, -2) == "/"
            name = name and name:lower()

            if name == "body" then
                if closing then
                    if in_body then
                        push("</div></div>")
                    end
                    push(raw)
                    in_body = false
                else
                    push(raw)
                    push('<div id="book-columns"><div id="book-inner">')
                    in_body = true
                    saw_body = true
                end
            else
                push(raw)
                if in_body and name then
                    if skip_name then
                        if name == skip_name then
                            if closing then
                                skip_depth = skip_depth - 1
                                if skip_depth == 0 then skip_name = nil end
                            elseif not self_closing then
                                skip_depth = skip_depth + 1
                            end
                        end
                    elseif SKIP_TAGS[name] and not closing and not self_closing then
                        skip_name, skip_depth = name, 1
                    elseif BLOCK_TAGS[name] then
                        new_para = true
                    end
                end
            end
        end
        if passthrough then
            push(src:sub(lt, stop))
        end
        pos = stop + 1
    end

    if not saw_body then
        return nil, "no body element"
    end
    return table.concat(out)
end

-- Attribute map of one tag's text, keys lower-cased.
local function parseAttrs(tag)
    local attrs = {}
    for key, quote, value in tag:gmatch("([%w_:%-]+)%s*=%s*([\"'])(.-)%2") do
        attrs[key:lower()] = value
    end
    return attrs
end

local function urlDecode(s)
    return (s:gsub("%%(%x%x)", function(h) return string.char(tonumber(h, 16)) end))
end

-- "OEBPS/text" + "../images/a.png" -> "OEBPS/images/a.png"
local function resolvePath(dir, href)
    href = urlDecode((href:gsub("[#?].*$", "")))
    local parts = {}
    local full = (dir ~= "" and (dir .. "/") or "") .. href
    for seg in full:gmatch("[^/]+") do
        if seg == ".." then
            parts[#parts] = nil
        elseif seg ~= "." then
            parts[#parts + 1] = seg
        end
    end
    return table.concat(parts, "/")
end

-- The paths (as they appear in the zip) of the reading-order XHTML documents.
function Kepub.contentDocuments(container_xml, read_entry)
    local opf_path
    for tag in container_xml:gmatch("<rootfile%s[^>]*>") do
        local attrs = parseAttrs(tag)
        if attrs["full-path"] then
            opf_path = urlDecode(attrs["full-path"])
            break
        end
    end
    if not opf_path then return nil, "no rootfile in container.xml" end
    local opf = read_entry(opf_path)
    if not opf then return nil, "cannot read " .. opf_path end

    local opf_dir = opf_path:match("^(.*)/[^/]*$") or ""
    local manifest = {}
    for tag in opf:gmatch("<item%s[^>]*>") do
        local a = parseAttrs(tag)
        if a.id and a.href then manifest[a.id] = a end
    end
    local docs, seen = {}, {}
    for tag in opf:gmatch("<itemref%s[^>]*>") do
        local item = manifest[parseAttrs(tag).idref or ""]
        if item then
            local mt = (item["media-type"] or ""):lower()
            local props = " " .. (item.properties or "") .. " "
            if (mt == "application/xhtml+xml" or mt == "text/html") and not props:find(" nav ", 1, true) then
                local path = resolvePath(opf_dir, item.href)
                if not seen[path] then
                    seen[path] = true
                    docs[#docs + 1] = path
                end
            end
        end
    end
    return docs
end

-- "/dir/Book.epub" -> "/dir/Book.kepub.epub"; nil when it is not an .epub path.
function Kepub.targetPath(epub_path)
    if type(epub_path) ~= "string" then return nil end
    local base = epub_path:match("^(.*)%.[eE][pP][uU][bB]$")
    if not base then return nil end
    if base:lower():sub(-6) == ".kepub" then return epub_path end
    return base .. KEPUB_SUFFIX
end

-- Converts src_path (an EPUB) into dst_path (a KEPUB). Returns true, or false plus a reason. src is
-- left alone; the caller decides what to remove. `archiver` defaults to KOReader's ffi/archiver.
function Kepub.convertFile(src_path, dst_path, archiver)
    archiver = archiver or require("ffi/archiver")
    local tmp_path = dst_path .. ".converting"
    local reader = archiver.Reader:new()
    if not reader:open(src_path) then
        return false, "cannot open EPUB: " .. tostring(reader.err)
    end

    local writer
    local function fail(reason)
        pcall(function() reader:close() end)
        if writer then pcall(function() writer:close() end) end
        pcall(os.remove, tmp_path)
        return false, reason
    end

    -- First pass: just learn the entry names.
    local entries = {}
    for entry in reader:iterate() do
        if entry.mode == "file" then entries[#entries + 1] = entry.path end
    end
    local function readEntry(path)
        return reader:extractToMemory(path)
    end

    local container = readEntry("META-INF/container.xml")
    if not container then return fail("not an EPUB (no META-INF/container.xml)") end
    local docs, err = Kepub.contentDocuments(container, readEntry)
    if not docs then return fail(err) end
    local is_content = {}
    for _, path in ipairs(docs) do is_content[path] = true end

    writer = archiver.Writer:new()
    if not writer:open(tmp_path, "zip") then
        return fail("cannot create output: " .. tostring(writer.err))
    end
    -- The EPUB container requires "mimetype" stored uncompressed, and libarchive can only choose
    -- the compression for the whole archive before the first entry, so everything is stored.
    -- Bigger on disk, valid everywhere.
    writer:setZipCompression("store")
    if not writer:addFileFromMemory("mimetype", "application/epub+zip") then
        return fail("cannot write mimetype: " .. tostring(writer.err))
    end

    local converted = 0
    for _, path in ipairs(entries) do
        if path ~= "mimetype" then
            local content = readEntry(path)
            if content == nil then
                return fail("cannot read " .. path .. ": " .. tostring(reader.err))
            end
            if is_content[path] then
                local new_content = Kepub.convertXhtml(content)
                if new_content then
                    content = new_content
                    converted = converted + 1
                end
            end
            if not writer:addFileFromMemory(path, content) then
                return fail("cannot write " .. path .. ": " .. tostring(writer.err))
            end
        end
    end
    reader:close()
    writer:close()

    if converted == 0 then
        pcall(os.remove, tmp_path)
        return false, "no content document could be converted"
    end
    local renamed, rename_err = os.rename(tmp_path, dst_path)
    if not renamed then
        pcall(os.remove, tmp_path)
        return false, "cannot move result into place: " .. tostring(rename_err)
    end
    return true
end

return Kepub
