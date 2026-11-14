-- Pandoc filter that turns the chapters, written for reading on GitHub, into
-- one book.
--
--   * A chapter title "3. Slope" loses its number: LaTeX numbers chapters.
--     A title with no number (Preface, Glossary) becomes an unnumbered chapter.
--   * The first chapter of each part gets a part page before it.
--   * The "Previous: ... Next: ..." line at the end of a chapter is dropped.
--   * A link to a file in the repository becomes a link to that file on GitHub.
--   * A code block is set in small type, with long lines wrapped.

local REPOSITORY =
  "https://github.com/Ghost---Shadow/squiggly-line-theorem/blob/main/"

local PART_BEFORE_CHAPTER = {
  ["1."] = "The theorem",
  ["8."] = "Networks",
  ["13."] = "The same tools elsewhere",
}

local function to_repository_url(target)
  local is_web_link = target:match("^%a[%w+.-]*:")
  local is_anchor = target:match("^#")
  if is_web_link or is_anchor then
    return nil
  end
  local path = "book/" .. target
  local replaced = 1
  while replaced > 0 do
    path, replaced = path:gsub("[^/]+/%.%./", "", 1)  -- "book/../lean" is "lean"
  end
  return REPOSITORY .. path
end

function Link(link)
  local url = to_repository_url(link.target)
  if url then
    link.target = url
  end
  return link
end

function Header(header)
  if header.level ~= 1 then
    return nil
  end
  local first = header.content[1]
  local chapter_number = first and first.t == "Str" and first.text:match("^%d+%.$")
  if not chapter_number then
    header.classes:insert("unnumbered")
    return header
  end
  table.remove(header.content, 1)
  if header.content[1] and header.content[1].t == "Space" then
    table.remove(header.content, 1)
  end
  local part_title = PART_BEFORE_CHAPTER[chapter_number]
  if part_title then
    return { pandoc.RawBlock("latex", "\\part{" .. part_title .. "}"), header }
  end
  return header
end

function Para(paragraph)
  local first = paragraph.content[1]
  local is_navigation = first and first.t == "Str"
    and (first.text == "Previous:" or first.text == "Next:")
  if is_navigation then
    return {}
  end
  return nil
end

function CodeBlock(block)
  return pandoc.RawBlock("latex",
    "\\begin{Verbatim}[breaklines,breakanywhere,fontsize=\\footnotesize]\n"
      .. block.text .. "\n\\end{Verbatim}")
end
