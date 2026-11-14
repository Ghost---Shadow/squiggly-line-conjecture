-- Pandoc filter that turns the chapters, written for reading on GitHub, into
-- pages of a static site.
--
--   * A link to a chapter file becomes a link to its .html page.
--   * A link to another file in the repository becomes a link to that file
--     on GitHub.
--   * A web link and a link to an anchor on the same page are left alone.
--   * An image "../graphs/x.png" becomes "graphs/x.png".

local REPOSITORY =
  "https://github.com/Ghost---Shadow/squiggly-line-theorem/blob/main/"

local function split_anchor(target)
  local path, anchor = target:match("^([^#]*)(#.*)$")
  if path then
    return path, anchor
  end
  return target, ""
end

local function is_chapter_file(path)
  return path:match("^%d%d%-[%w-]+%.md$")
    or path == "glossary.md"
    or path == "how-to-cite.md"
    or path == "README.md"
end

local function to_repository_url(path)
  local full = "book/" .. path
  local replaced = 1
  while replaced > 0 do
    full, replaced = full:gsub("[^/]+/%.%./", "", 1)  -- "book/../lean" is "lean"
  end
  return REPOSITORY .. full
end

function Link(link)
  local target = link.target
  local is_web_link = target:match("^%a[%w+.-]*:")
  local is_anchor = target:match("^#")
  if is_web_link or is_anchor or target == "" then
    return nil
  end
  local path, anchor = split_anchor(target)
  if path == "README.md" then
    link.target = "index.html" .. anchor
  elseif is_chapter_file(path) then
    link.target = path:gsub("%.md$", ".html") .. anchor
  elseif path:match("^%.%./") or path == "pdf/build.sh" or path == "CITATION.bib" then
    link.target = to_repository_url(path) .. anchor
  end
  return link
end

function Image(image)
  local path = image.src:match("^%.%./(graphs/.+)$")
  if path then
    image.src = path
  end
  return image
end
