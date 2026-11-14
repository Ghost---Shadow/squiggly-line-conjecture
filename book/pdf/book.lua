-- Pandoc filter that turns the chapters, written for reading on GitHub, into
-- one book.
--
--   * A chapter title "3. Slope" loses its number: LaTeX numbers chapters.
--     A title with no number (Preface, Glossary) becomes an unnumbered chapter.
--   * The first chapter of each part gets a part page before it.
--   * The "Previous: ... Next: ..." line at the end of a chapter is dropped.
--   * A link to a file in the repository becomes a link to that file on GitHub.
--   * A code block is set in small type, with long lines wrapped.
--   * A table gets column widths, so that it fits the page.
--   * Sections of an unnumbered chapter are unnumbered too.

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

local in_unnumbered_chapter = false

function Header(header)
  if header.level ~= 1 then
    if in_unnumbered_chapter then
      header.classes:insert("unnumbered")  -- no "0.1" inside the preface
    end
    return header
  end
  local first = header.content[1]
  local chapter_number = first and first.t == "Str" and first.text:match("^%d+%.$")
  in_unnumbered_chapter = not chapter_number
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

-- A table written for GitHub has no column widths, so LaTeX would set every
-- cell on one line and run off the page. Give each column a share of the
-- page in proportion to how much it holds.
local LONGEST_CELL_COUNTED = 45   -- a longer cell wraps instead of widening
local ROOM_PER_LETTER_OF_A_NAME = 1.6  -- a name in code type cannot break

local function count_letters(text)
  return utf8.len(text) or #text
end

local function longest_word(text)
  local longest = 0
  for word in text:gmatch("%S+") do
    longest = math.max(longest, count_letters(word))
  end
  return longest
end

function Table(table_block)
  local simple = pandoc.utils.to_simple_table(table_block)
  local weights = {}
  local function measure(cells)
    for column, cell in ipairs(cells) do
      local text = pandoc.utils.stringify(pandoc.Div(cell))
      local cell_length = math.min(count_letters(text), LONGEST_CELL_COUNTED)
      local name_length = longest_word(text) * ROOM_PER_LETTER_OF_A_NAME
      weights[column] = math.max(weights[column] or 4, cell_length, name_length)
    end
  end
  measure(simple.header)
  for _, row in ipairs(simple.rows) do
    measure(row)
  end
  local total = 0
  for _, weight in ipairs(weights) do
    total = total + weight
  end
  for column, weight in ipairs(weights) do
    simple.widths[column] = weight / total
  end
  return pandoc.utils.from_simple_table(simple)
end

function CodeBlock(block)
  return pandoc.RawBlock("latex",
    "\\begin{Verbatim}[breaklines,breakanywhere,fontsize=\\footnotesize]\n"
      .. block.text .. "\n\\end{Verbatim}")
end
