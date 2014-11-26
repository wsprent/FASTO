;;; fasto-mode.el --- major mode for editing FASTO source files

;; Written by Niels G. W. Serup <ngws@metanohi.name> in 2014.
;;
;; Based on futhark-mode.el <https://github.com/HIPERFIT/futhark>
;; written by Troels Henriksen <athas@sigkill.dk> and Niels
;; G. W. Serup in 2013-2014.

;;; Commentary:
;; This mode provides the following features for FASTO source files:
;;   + syntax highlighting
;;   + experimental, automatic indentation
;;   + interactive functions
;;
;; To load fasto-mode automatically on Emacs startup, put this file in
;; your load path (e.g. ".emacs.d") and add the following line to your
;; .emacs:
;;
;;   (require 'fasto-mode)
;;
;; This will also tell your Emacs that .fo files are handled by
;; fasto-mode.
;;
;; Local keybindings:
;;
;;   C-c C-l: Run the FASTO interpreter (fasto -i) on the current
;;            file and show the output in another buffer.  fasto-mode
;;            will guess the location of fasto unless you globally
;;            define `fasto-binary'.
;;
;; Change keybindings in `fasto-mode-map` and add hooks to
;; `fasto-mode-hook`.
;;
;; Report bugs to Niels.

;;; Code:

(require 'cl)

(defvar fasto-mode-hook nil
  "Hook for fasto-mode -- run whenever the mode is entered.")

(defvar fasto-mode-map
  (let ((map (make-keymap)))
    map)
  "Keymap for fasto-mode.")

(defcustom fasto-indent-level 2
  "Indentation of blocks in FASTO."
  :group 'fasto
  :type '(integer))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.fo\\'" . fasto-mode))

(defconst fasto-keywords
  '("if" "then" "else" "let" "in" "fun" "op")
  "A list of FASTO keywords.")

(defconst fasto-builtins
  '("iota" "replicate" "map" "reduce" "read" "write" "not")
  "A list of FASTO builtin SOACs, functions and unary operators.")

(defconst fasto-types
  '("int" "bool" "char")
  "A list of FASTO types.")

(defvar fasto-font-lock
  `(
    ;; Keywords
    (,(concat "\\<" (regexp-opt fasto-keywords t) "\\>") . font-lock-keyword-face)

    ;; Builtins
    (,(concat "\\<" (regexp-opt fasto-builtins t) "\\>") . font-lock-builtin-face)
    
    ;; Types
    (,(concat "\\<" (regexp-opt fasto-types t) "\\>") . font-lock-type-face)
    
    ;; Function definitions
    ; TODO.  Seems tricky.

    ;; Constants
    ;;; Characters
    ("'\\([^\\'\n]\\|\\\\[a-z']\\)'" . font-lock-constant-face)
    ;;; Booleans
    ("\\<\\(True\\|False\\)\\>" . font-lock-constant-face)

    ;; Variables
    ("[[:alpha:]][[:alnum:]]*" . font-lock-variable-name-face)
    )
  "Highlighting expressions for FASTO.")

(defvar fasto-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; Define the // line comment syntax.
    (modify-syntax-entry ?/ ". 124b" st)
    (modify-syntax-entry ?\n "> b" st)
    st)
  "Syntax table used in `fasto-mode'.")


;;; Indentation

;; fasto-mode uses heuristics to determine how much to indent a line.
;; For the most part, this gives an okay result.  Some multi-line
;; things don't work well.

(defun fasto-indent-line ()
  "Indent current line as FASTO code."
  (interactive)
  (let ((savep (> (current-column) (current-indentation)))
    (indent (or (fasto-calculate-indentation)
                (current-indentation))))
    (if savep
        (save-excursion (indent-line-to indent))
      (indent-line-to indent))))

;; Keywords on which to base indentation.
(defstruct fasto-indkwd name level pos)

(defun fasto-indkwd-column (k)
  (save-excursion
    (goto-char (fasto-indkwd-pos k))
    (current-column)))

(defun fasto-indkwd-linum (k)
  (line-number-at-pos (fasto-indkwd-pos k)))

(defun fasto-indkwd-compare (a b)
  "Compare two positions of keywords to see which keyword should
be indented against.  Prefer the keywords closest to you and with
least existing indentation."
  (or (> (fasto-indkwd-linum a) (fasto-indkwd-linum b))
      (and (= (fasto-indkwd-linum a) (fasto-indkwd-linum b))
           (< (fasto-indkwd-column a) (fasto-indkwd-column b)))))

(defun fasto-backward-part ()
  "Try to jump back one sexp.  The net effect seems to be that it
works ok."
  (ignore-errors (backward-sexp 1) t))

(defun fasto-calculate-indentation ()
  "Calculate the indentation for the current line.  In general,
prefer as little indentation as possible to visually separate the
code, but use more detailed indentation with \"if\", \"then\",
\"else\", \"let\", and \"in\"."
  (let ((parse-sexp-lookup-properties t)
        (parse-sexp-ignore-comments t)
        (oldp (point)))
    (save-excursion
      (beginning-of-line-text)

      ;; Align comment to next non-comment line.
      (when (looking-at "//")
        (forward-comment (buffer-size)))

      (or (cond

           ;; Function definitions to column 0.
           ((looking-at "fun\\>")
            0)

           ;; Closing paren and comma indents to opening paren.
           ((looking-at ",\\|\\s)")
            (ignore-errors
              (backward-up-list 1)
              (current-column)))

           ;; Make "in" align to nearest "let".
           ((looking-at "in")
            (when
                ;; Do not use the first-on-line variant, as we're
                ;; interested in a matching "let", not in a short
                ;; indentation.
                (fasto-find-keyword-backward "let"))
              (current-column))

           ;; Make "then" align to nearest "if".
           ((looking-at "then")
            (when (fasto-find-keyword-first-on-line-backward "if")
              (current-column)))

           ;; Make "else if" align to nearest "else" or "if", instead
           ;; of nearest "then", to avoid very long lines if chained.
           ((looking-at "else[[:space:]]+if")
            (let ((p
                   (or
                    (search-backward "else" 0 t)
                    (search-backward "if" 0 t))))
              (when p
                (goto-char p)
                (current-column))))

           ;; Make "else" align to nearest "then".
           ((looking-at "else")
            (when (fasto-find-keyword-first-on-line-backward "then")
              (current-column))))

          ;; Otherwise, if the previous line ends with "in", indent to
          ;; the matching "let".
          (save-excursion
            (when (and (fasto-backward-part)
                       (looking-at "in")
                       (fasto-find-keyword-backward "let"))
              (current-column)))

          ;; Otherwise, if the previous line ends with "=", indent to
          ;; the matching "let" if it's close.
          (save-excursion
            (when (and (fasto-backward-part)
                       (looking-at "=")
                       (let ((linum (line-number-at-pos)))
                         (when (fasto-find-keyword-backward "let")
                           (= linum (line-number-at-pos)))))
              (+ fasto-indent-level (current-column))))

          ;; Otherwise, try to align to a control keyword if the
          ;; previous line does not end with a comma.
          (when (not (save-excursion
                       (when (fasto-backward-part)
                         (end-of-line)
                         (goto-char (1- (point)))
                         (looking-at ","))))
            (let ((indkwds (list
                            ;; Don't further indent lines after "in".
                            (make-fasto-indkwd :name "in" :level 0)
                            ;; Don't consider "let"-heavy lines reason
                            ;; to further indent.
                            (make-fasto-indkwd :name "let" :level 0)
                            ;; The rest is more obvious.
                            (make-fasto-indkwd :name "else" :level 1)
                            (make-fasto-indkwd :name "then" :level 1)
                            (make-fasto-indkwd :name "for" :level 1)
                            (make-fasto-indkwd :name "fun" :level 1))))
              (mapc (lambda (k)
                      (save-excursion
                        (when (fasto-find-keyword-first-on-line-backward
                               (fasto-indkwd-name k))
                          (setf (fasto-indkwd-pos k) (point))))) indkwds)
              (let ((indkwd-best
                     (car (sort (remove-if
                                 (lambda (k) (null (fasto-indkwd-pos k)))
                                 indkwds)
                                'fasto-indkwd-compare))))
                (when indkwd-best
                  (save-excursion
                    (goto-char (fasto-indkwd-pos indkwd-best))
                    (+ (* fasto-indent-level (fasto-indkwd-level indkwd-best))
                       (current-column)))))))

          ;; Otherwise, try to align to the top element in an array
          ;; literal or similar structure.
          (when (ignore-errors (backward-up-list 1) t)
            (goto-char (1+ (point)))
            (or
             (save-excursion
               (when (re-search-forward "[^[:space:]]" (line-end-position) t)
                 (goto-char (1- (point)))
                 (current-column)))
             ;; If the top element is not on the same line as the
             ;; opening paren, use 1 indent level relative to the
             ;; previous line.
             (save-excursion
               (goto-char oldp)
               (forward-line -1)
               (beginning-of-line-text)
               (+ fasto-indent-level (current-column)))
             ))

          ;; In all remaining cases (what are those?), keep the
          ;; current indentation.
          ))))

(defun fasto-find-keyword-first-on-line-backward (word &optional is-at-in)
  "Do the same as `fasto-find-keyword-backward', except if one line
  has several matching keywords, set the mark at the first one."
  (let ((is-at-in (or is-at-in (looking-at "in"))))
    (when (fasto-find-keyword-backward word is-at-in)
      (let ((p (point)))
        (while (and (when (fasto-find-keyword-backward word is-at-in)
                      (not (= (point) p)))
                    (= (line-number-at-pos) (line-number-at-pos p)))
          (setq p (point)))
        (goto-char p))
      t)))

(defun fasto-find-keyword-backward (word &optional is-at-in)
  "Find a keyword before the current position.  Set mark and
return t if found; return nil otherwise."
  (let ((oldp (point))
        ;; We need to count "if"s and "else"s to properly indent.
        (missing-ifs 0)
        ;; The same with "let" and "in", though only if we start at
        ;; "in".
        (missing-outs 0)
        ;; "in" is special, since starting at it means aligning it to
        ;; the correct "let", which means counting.  In all other
        ;; cases, we just want the least space-using indentation.
        (orig-in (or is-at-in (looking-at "in")))
        ;; Only look in the current paren-delimited code.
        (topp (or (ignore-errors
                    (save-excursion
                      (backward-up-list 1)
                      (point)))
                  -1)))
    (while (and (not (bobp))
                (> (point) topp)
                (fasto-backward-part)
                (or (not (or (looking-at word)
                             (looking-at "fun")))
                    (> missing-ifs 0)
                    (> missing-outs 0)
                    ))
      (cond ((looking-at "if")
             (setq missing-ifs (max 0 (1- missing-ifs))))
            ((looking-at "else")
             (incf missing-ifs))
            (orig-in
              (cond
               ((looking-at "let")
                (setq missing-outs (max 0 (1- missing-outs))))
               ((looking-at "in")
                (incf missing-outs))))))
    (if (and (looking-at word)
             (not (= (point) oldp)))
        t
      (goto-char oldp)
      nil)))


(define-derived-mode fasto-mode fundamental-mode "FASTO"
  "Major mode for editing FASTO source files."
  :syntax-table fasto-mode-syntax-table
  (set (make-local-variable 'font-lock-defaults) '(fasto-font-lock))
  (set (make-local-variable 'indent-line-function) 'fasto-indent-line)
  (set (make-local-variable 'comment-start) "//")
  (set (make-local-variable 'comment-padding) " "))


;; Interactive functions, keybindings and related parts

(defvar fasto-output-font-lock
  (append
   '(
     ("Program is:" . font-lock-comment-face)
     ("Result:" . font-lock-comment-face)
     )
   fasto-font-lock))

(define-derived-mode fasto-output-mode fasto-mode "fasto output"
  "Major mode for viewing fasto output."
  (set (make-local-variable 'font-lock-defaults) '(fasto-output-font-lock)))

(defvar fasto-binary nil
  "The global location of the fasto binary.")

(defun fasto-interpret (file &optional fasto-bin)
  "Interpret a FASTO file.  If called interactively, guess the
path of the binary 'fasto' and run that on the file of the
current buffer.

`file' is the file to interpret.

`fasto-bin' is the location of the binary.  If you set
`fasto-binary', that value will be used.
"
  (interactive (list (buffer-file-name)))
  ; In the handed out code, tests are located in "src/", and the
  ; binary in "bin/", so we assume this is the case here.
  (let ((bufname "*FASTO interpreter output*")
        (max-mini-window-height 0)
        (fasto-bin (or fasto-bin
                       fasto-binary
                       (concat (file-name-directory file) "../bin/fasto"))))
    (shell-command
     (concat fasto-bin " -i " file) bufname)
    ; Set the mode of the new buffer.
    (with-current-buffer bufname
      (fasto-output-mode))))

(define-key fasto-mode-map (kbd "C-c C-l") 'fasto-interpret)


(provide 'fasto-mode)

;;; fasto-mode.el ends here
