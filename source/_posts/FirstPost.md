---
title: Markdown note
top: false
cover: false
toc: true
mathjax: true
tags: what tag
categories: 
  - [category A]
  - [category B]
permalinks: what_url
date: 1900-01-02 00:00:00
password:
summary:
updated: 2600-08-78
---


# Tips of browser real-time autosync
terminal commond: npm install hexo-browsersync -\-save
With this plugin, after first time launching "hexo s", it should be able to automatically sync the browser content with the newset update in *.md files. It will show something like this:
> [Browsersync] Access URLs:
> UI: http://localhost:3001
> UI External: http://localhost:3001
> INFO  Start processing
> INFO  Hexo is running at http://localhost:4000 . Press Ctrl+C to stop.  

--------------

# Section title
To create section title, use "# title_name". Number of '#' is the sub-sectioin level. Maximum of '#' is 6. For example,
# L1
## L2
### L3
###### L6

--------------

# Quote
To quote, use '> line_to_quote' to quote. For example,
> this is the line quoted  

quote can be nested by adding '>'
> quote
>> subquote  

--------------

# Add image
To add image in markdown, use '![optional tag name](image path)' to add image.
optional tag name: the name is used to display when image cannot be shown.
image path: could be neither the local image path, e.g. /use/download/image.jpg, or url, e.g. www.abc.com/pic/image.jpg
![landscape](landscape.jpeg)

### Tips in adding image in hexo
Changing 'post_asset_folder' to be true in _config.yml will create a folder with the same name as the post_name under _post folder when calling 'hexo new post_name' and the image can be put in this folder and referenced, e.g. _post/post_name/image.jpg

--------------

# Add url link
To add link, use '[name to display](url)', e.g. "[GG]\(https://www.google.com)" gives
[GG](https://www.google.com)

--------------

# italic and bold font
__Text enclosed by two '*' or '_' is bold.__
_Text enclosed by one '*' or \'\_\' is italic._  
Here \'\*\' is the same as \'\_\', three \'\*\' is italic+bold
