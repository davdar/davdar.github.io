# How I Vim

By David Darais.

[this file](howivim.md) as Markdown.

You may want to keep one of these cheat sheets around while learning Vim.

- [https://vim.rtorr.com]
- [https://www.cs.cmu.edu/~15131/f17/topics/vim/vim-cheatsheet.pdf]
- [https://vimsheet.com]
- [http://i.imgur.com/YLInLlY.png]
- [http://michael.peopleofhonoronly.com/vim/]
- [http://www.viemu.com/vi-vim-cheat-sheet.gif]

## Modes

Normal mode: 

This is the mode that vim starts in. All letter that you press are not
interpreted as “input this character”, rather they are interpreted as special
commands. *You should always be in normal mode as your “default” mode.*

Input mode:

You can get into input mode by a number of commands, the most common being `i`.
To get out of insert mode (i.e., back into normal mode), press `Esc`, `Ctl-c`
or `Ctl-[`. I remember hearing that `Ctl-c` is slightly different, and `Esc`
and `Ctl-[` are identical. Google it if you're curious. I remap my caps lock
key to `Esc`. I did this to train myself in preparation for a mac laptop with
no physical escape key. I never got one, and now my brain is trained to whack
caps lock to get back to normal mode, so I just left it.

## Moving Around

- `h`: left
- `j`: down (looks almost like a down arrow)
- `k`: up
- `l`: right

The keys `hjkl` are the arrows `←↓↑→`

Exercise:

work your way through this maze (found [here][1]):

    ___________________________________ 
    | _____ |   | ___ | ___ ___ | |   | |
    | |   | |_| |__ | |_| __|____ | | | |
    | | | |_________|__ |______ |___|_| |
    | |_|   | _______ |______ |   | ____|
    | ___ | |____ | |______ | |_| |____ |
    |___|_|____ | |   ___ | |________ | |
    |   ________| | |__ | |______ | | | |
    | | | ________| | __|____ | | | __| |
    |_| |__ |   | __|__ | ____| | |_| __|
    |   ____| | |____ | |__ |   |__ |__ |
    | |_______|_______|___|___|___|_____|
      
[1]: https://www.asciiart.eu/art-and-design/mazes

 command            | effect                                     | mnemonic 
--------------------|--------------------------------------------|----------
 `h`, `j`, `k`, `l` | left, down, up, right                      |          
 `Ctl-u`            | page up                                    | up       
 `Ctl-d`            | page up                                    | do       
 `gg`               | first line                                 |          
 `G`                | last line                                  |          
 `<n>gg`            | line <n>                                   |          
 `Ctl-o`            | jump back                                  |          
 `Ctl-i`            | jump forward                               |          
 `w`, `W`           | small word, big word                       | word     
 `e`, `E`           | small end-of-word, big end-of-word         | end      
 `b`, `B`           | small back-word, big back-word             | back     
 `\|`               | beginning of line                          |          
 `^`                | first non-space character on               |          
 `$`                | end of line                                |          
 `%`                | jump to matching bracket                   |          
 `gj`, `gk`         | up and down inside softwrap lines          |          

## Getting into Insert Mode

 command   | effect                                      | mnemonic 
-----------|---------------------------------------------|----------
 `i`       | insert mode before cursor                   | insert   
 `I`       | insert mode at beginning of line            |          
 `a`       | insert mode after cursor                    | after    
 `A`       | insert mode at end of line                  |          
 `o`       | insert mode after making a new line below   |          
 `O`       | insert mode after making a new line above   |          

## Undo/Redo

 command   | effect                                     | mnemonic 
-----------|--------------------------------------------|----------
 `u`       | undo                                       | undo     
 `Ctl-r`   | redo                                       | redo     

## Selecting and Searching Text

 command | effect                                     | mnemonic 
---------|--------------------------------------------|----------
 `v`     | selection starting with cursor position    | visual   
 `V`     | selection starting with whole line         |          
 `Ctl-v` | column-selection starting with cursor      |          
 `/`     | search (regex)                             |          
 `*`     | search for word underneath cursor          |          
 `n`     | jump to next search result                 | next     
 `N`     | jump to previous search result             |          
 `vab`   | select a parens                            |
 `vib`   | select in parens                           |
 `vi[`   | select in square brackets []               |
 `vi{`   | select in curly brackets {}                |

## Slicing and Dicing Text

 command           | effect                                           | mnemonic 
-------------------|--------------------------------------------------|----------
 `d<motion>`       | delete and copy text under <motion>              | delete   
 `dd`              | delete and copy whole line                       |          
 `D`               | delete and copy text until end of line           |          
 `c<motion>`       | like “d” but ends up in insert mode              | change   
 `cc`              | like “dd” …                                      |          
 `C`               | like “D” …                                       |          
 `y<motion>`       | copy text under <motion> to Vim clipboard        | yank     
 `yy`              | like “dd” …                                      |          
 `Y`               | (should be) like “D” …                           |          
 `yib`             | yank in parens ()                                |
 `yi[`             | yank in square brackets []                       |
 `yi{`             | yank in curly brackets {}                        |
 `p`               | paste after cursor                               | paste    
 `P`               | paste behind cursor                              |          
 `x`               | delete and copy character under cursor           |          
 `xp`              | swap characters                                  |          
 `r<char>`         | replace character under cursor with <char> | replace  
 `R`               | like insert mode but overwrites text             | replace  
 `~`               | change character case (upper/lower)              |          
 `"0p`             | paste the last thing yanked                      |          
 `"ay`             | yank to register “a”                             |          
 `"ap`             | paste from register “a”                          |          
 `:reg`            | look at clipboard registers                      |          
 `gq`              | line-wrap paragraph                              |          
 `J`               | un-line-wrap (join with spaces) lines            | join     

## Meta Commands

 command                 | effect                                     | mnemonic 
-------------------------|--------------------------------------------|----------
 `.`         | repeat the last command                                |          
 `<n><cmd>`  | repeat <cmd> <n> times                                 |          

## Files and Buffers

 command             | effect                                     | mnemonic 
---------------------|--------------------------------------------|----------
 `:e <name>`         | open <name> and start editing        | edit     
 `:w`                | save this buffer                           | write    
 `:wa`               | save all buffers                           |          
 `:q`                | quit                                       | quit     
 `:q!`               | quit I promise                             |          
 `:wq`               | save and quit                              |          
 `:ls`               | show all buffers                           | list     
 `:b <name>`         | switch to buffer                           | buffer   
 `:b#`               | switch to last buffer                      |          
 `:split`            | horizontal split                           |          
 `:vsplit`           | vertical split                             |          
 `:close`            | close a split panel                        |          
 `:help <cmd>`       | get help on a command                      |          
 `Ctl-w h`           | go to panel to the left                    |          
 `Ctl-w j`           | go to panel below                          |          
 `Ctl-w k`           | go to panel above                          |          
 `Ctl-w l`           | go to panel to the right                   |          
 `Ctl-w +`           | make panel taller                          |          
 `Ctl-w -`           | make panel shorter                         |          
 `Ctl-w <`           | make panel thinner                         |          
 `Ctl-w >`           | make panel wider                           |          


## Miscellaneous

 command            | effect                              | mnemonic 
--------------------|-------------------------------------|---------
 `:set spell`       | enable spell check on all buffers   |          
 `:set local spell` | enable spell check on this buffer   |          
 `zg`               | add word to dictionary              |         

## Plugins

- Pathogen (plugin manager)
- NERDTree (directory browser)
