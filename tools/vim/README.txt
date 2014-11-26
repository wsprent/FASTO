Vim syntax highlighting for Fasto.
Created by Oleksandr Shturmov <oleks@oleks.info> on November 1, 2014.

To install:

1. Copy fasto.vim into your ~/.vim/syntax/ (create the directory if it doesn't
already exist).

2. Add the following line to your ~/.vimrc. This will make sure that any .fo
file is recognised as a fasto file. It is important that fasto.vim is present
in ~/.vim/syntax/ for syntax highlighting to work.

au BufNewFile,BufRead *.fo setlocal ft=fasto
