(eval-when-compile (require 'cl-lib))

(defgroup eshell-util nil
  "This is general utility code, meant for use by Eshell itself."
  :tag "General utilities"
  :group 'eshell)

;;; User Variables:

(defcustom eshell-stringify-t t
  "If non-nil, the string representation of t is 't'.
If nil, t will be represented only in the exit code of the function,
and not printed as a string.  This causes Lisp functions to behave
similarly to external commands, as far as successful result output."
  :type 'boolean
  :group 'eshell-util)

(defcustom eshell-group-file "/etc/group"
  "If non-nil, the name of the group file on your system."
  :type '(choice (const :tag "No group file" nil) file)
  :group 'eshell-util)

(defcustom eshell-passwd-file "/etc/passwd"
  "If non-nil, the name of the passwd file on your system."
  :type '(choice (const :tag "No passwd file" nil) file)
  :group 'eshell-util)

(defcustom eshell-hosts-file "/etc/hosts"
  "The name of the /etc/hosts file."
  :type '(choice (const :tag "No hosts file" nil) file)
  :group 'eshell-util)

(defcustom eshell-handle-errors t
  "If non-nil, Eshell will handle errors itself.
Setting this to nil is offered as an aid to debugging only."
  :type 'boolean
  :group 'eshell-util)

(defcustom eshell-private-file-modes 384 ; umask 177
  "The file-modes value to use for creating \"private\" files."
  :type 'integer
  :group 'eshell-util)

(defcustom eshell-private-directory-modes 448 ; umask 077
  "The file-modes value to use for creating \"private\" directories."
  :type 'integer
  :group 'eshell-util)

(defcustom eshell-tar-regexp
  "\\.t\\(ar\\(\\.\\(gz\\|bz2\\|xz\\|Z\\)\\)?\\|gz\\|a[zZ]\\|z2\\)\\'"
  "Regular expression used to match tar file names."
  :version "24.1"                       ; added xz
  :type 'regexp
  :group 'eshell-util)

(defcustom eshell-convert-numeric-arguments t
  "If non-nil, converting arguments of numeric form to Lisp numbers.
Numeric form is tested using the regular expression
`eshell-number-regexp'.

NOTE: If you find that numeric conversions are interfering with the
specification of filenames (for example, in calling `find-file', or
some other Lisp function that deals with files, not numbers), add the
following in your init file:

  (put 'find-file 'eshell-no-numeric-conversions t)

Any function with the property `eshell-no-numeric-conversions' set to
a non-nil value, will be passed strings, not numbers, even when an
argument matches `eshell-number-regexp'."
  :type 'boolean
  :group 'eshell-util)

(defcustom eshell-number-regexp "-?\\([0-9]*\\.\\)?[0-9]+\\(e[-0-9.]+\\)?"
  "Regular expression used to match numeric arguments.
If `eshell-convert-numeric-arguments' is non-nil, and an argument
matches this regexp, it will be converted to a Lisp number, using the
function `string-to-number'."
  :type 'regexp
  :group 'eshell-util)

(defcustom eshell-ange-ls-uids nil
  "List of user/host/id strings, used to determine remote ownership."
  :type '(repeat (cons :tag "Host for User/UID map"
                       (string :tag "Hostname")
                       (repeat (cons :tag "User/UID List"
                                     (string :tag "Username")
                                     (repeat :tag "UIDs" string)))))
  :group 'eshell-util)

;;; Internal Variables:

(defvar eshell-group-names nil
  "A cache to hold the names of groups.")

(defvar eshell-group-timestamp nil
  "A timestamp of when the group file was read.")

(defvar eshell-user-names nil
  "A cache to hold the names of users.")

(defvar eshell-user-timestamp nil
  "A timestamp of when the user file was read.")

(defvar eshell-host-names nil
  "A cache the names of frequently accessed hosts.")

(defvar eshell-host-timestamp nil
  "A timestamp of when the hosts file was read.")

;;; Functions:

(defsubst eshell-under-windows-p ()
  "Return non-nil if we are running under MS-DOS/Windows."
  (memq system-type '(ms-dos windows-nt)))

(defmacro eshell-condition-case (tag form &rest handlers)
  "If `eshell-handle-errors' is non-nil, this is `condition-case'.
Otherwise, evaluates FORM with no error handling."
  (declare (indent 2))
  (if eshell-handle-errors
      `(condition-case-unless-debug ,tag
           ,form
         ,@handlers)
    form))

(defun eshell-find-delimiter
  (open close &optional bound reverse-p backslash-p)
  "From point, find the CLOSE delimiter corresponding to OPEN.
The matching is bounded by BOUND.
If REVERSE-P is non-nil, process the region backwards.
If BACKSLASH-P is non-nil, and OPEN and CLOSE are the same character,
then quoting is done by a backslash, rather than a doubled delimiter."
  (save-excursion
    (let ((depth 1)
          (bound (or bound (point-max))))
      (if (if reverse-p
              (eq (char-before) close)
            (eq (char-after) open))
          (forward-char (if reverse-p -1 1)))
      (while (and (> depth 0)
                  (funcall (if reverse-p '> '<) (point) bound))
        (let ((c (if reverse-p (char-before) (char-after))) nc)
          (cond ((and (not reverse-p)
                      (or (not (eq open close))
                          backslash-p)
                      (eq c ?\\)
                      (setq nc (char-after (1+ (point))))
                      (or (eq nc open) (eq nc close)))
                 (forward-char 1))
                ((and reverse-p
                      (or (not (eq open close))
                          backslash-p)
                      (or (eq c open) (eq c close))
                      (eq (char-before (1- (point)))
                          ?\\))
                 (forward-char -1))
                ((eq open close)
                 (if (eq c open)
                     (if (and (not backslash-p)
                              (eq (if reverse-p
                                      (char-before (1- (point)))
                                    (char-after (1+ (point)))) open))
                         (forward-char (if reverse-p -1 1))
                       (setq depth (1- depth)))))
                ((= c open)
                 (setq depth (+ depth (if reverse-p -1 1))))
                ((= c close)
                 (setq depth (+ depth (if reverse-p 1 -1))))))
        (forward-char (if reverse-p -1 1)))
      (if (= depth 0)
          (if reverse-p (point) (1- (point)))))))

(defun eshell-convert (string)
  "Convert STRING into a more native looking Lisp object."
  (if (not (stringp string))
      string
    (let ((len (length string)))
      (if (= len 0)
          string
        (if (eq (aref string (1- len)) ?\n)
            (setq string (substring string 0 (1- len))))
        (if (string-match "\n" string)
            (split-string string "\n")
          (if (and eshell-convert-numeric-arguments
                   (string-match
                    (concat "\\`\\s-*" eshell-number-regexp
                            "\\s-*\\'") string))
              (string-to-number string)
            string))))))

(defun eshell-sublist (l &optional n m)
  "Return from LIST the N to M elements.
If N or M is nil, it means the end of the list."
  (let ((a (copy-sequence l)))
    (if (and m (consp (nthcdr m a)))
        (setcdr (nthcdr m a) nil))
    (if n
        (setq a (nthcdr n a))
      (setq n (1- (length a))
            a (last a)))
    a))

(defvar eshell-path-env (getenv "PATH")
  "Content of $PATH.
It might be different from \(getenv \"PATH\"\), when
`default-directory' points to a remote host.")
(make-variable-buffer-local 'eshell-path-env)

(defun eshell-parse-colon-path (path-env)
  "Split string with `parse-colon-path'.
Prepend remote identification of `default-directory', if any."
  (let ((remote (file-remote-p default-directory)))
    (if remote
        (mapcar
         (lambda (x) (concat remote x))
         (parse-colon-path path-env))
      (parse-colon-path path-env))))

(defun eshell-split-path (path)
  "Split a path into multiple subparts."
  (let ((len (length path))
        (i 0) (li 0)
        parts)
    (if (and (eshell-under-windows-p)
             (> len 2)
             (eq (aref path 0) ?/)
             (eq (aref path 1) ?/))
        (setq i 2))
    (while (< i len)
      (if (and (eq (aref path i) ?/)
               (not (get-text-property i 'escaped path)))
          (setq parts (cons (if (= li i) "/"
                              (substring path li (1+ i))) parts)
                li (1+ i)))
      (setq i (1+ i)))
    (if (< li i)
        (setq parts (cons (substring path li i) parts)))
    (if (and (eshell-under-windows-p)
             (string-match "\\`[A-Za-z]:\\'" (car (last parts))))
        (setcar (last parts) (concat (car (last parts)) "/")))
    (nreverse parts)))

(defun eshell-to-flat-string (value)
  "Make value a string.  If separated by newlines change them to spaces."
  (let ((text (eshell-stringify value)))
    (if (string-match "\n+\\'" text)
        (setq text (replace-match "" t t text)))
    (while (string-match "\n+" text)
      (setq text (replace-match " " t t text)))
    text))

(defmacro eshell-for (for-var for-list &rest forms)
  "Iterate through a list."
  (declare (obsolete dolist "24.1"))
  (declare (indent 2))
  `(let ((list-iter ,for-list))
     (while list-iter
       (let ((,for-var (car list-iter)))
         ,@forms)
       (setq list-iter (cdr list-iter)))))

(defun eshell-flatten-list (args)
  "Flatten any lists within ARGS, so that there are no sublists."
  (let ((new-list (list t)))
    (dolist (a args)
      (if (and (listp a)
               (listp (cdr a)))
          (nconc new-list (eshell-flatten-list a))
        (nconc new-list (list a))))
    (cdr new-list)))

(defun eshell-uniqify-list (l)
  "Remove occurring multiples in L.  You probably want to sort first."
  (let ((m l))
    (while m
      (while (and (cdr m)
                  (string= (car m)
                           (cadr m)))
        (setcdr m (cddr m)))
      (setq m (cdr m))))
  l)

(defun eshell-stringify (object)
  "Convert OBJECT into a string value."
  (cond
   ((stringp object) object)
   ((and (listp object)
         (not (eq object nil)))
    (let ((string (pp-to-string object)))
      (substring string 0 (1- (length string)))))
   ((numberp object)
    (number-to-string object))
   (t
    (unless (and (eq object t)
                 (not eshell-stringify-t))
      (pp-to-string object)))))

(defsubst eshell-stringify-list (args)
  "Convert each element of ARGS into a string value."
  (mapcar 'eshell-stringify args))

(defsubst eshell-flatten-and-stringify (&rest args)
  "Flatten and stringify all of the ARGS into a single string."
  (mapconcat 'eshell-stringify (eshell-flatten-list args) " "))

(defsubst eshell-directory-files (regexp &optional directory)
  "Return a list of files in the given DIRECTORY matching REGEXP."
  (directory-files (or directory default-directory)
                   directory regexp))

(defun eshell-regexp-arg (prompt)
  "Return list of regexp and prefix arg using PROMPT."
  (let* (;; Don't clobber this.
         (last-command last-command)
         (regexp (read-from-minibuffer prompt nil nil nil
                                       'minibuffer-history-search-history)))
    (list (if (string-equal regexp "")
              (setcar minibuffer-history-search-history
                      (nth 1 minibuffer-history-search-history))
            regexp)
          (prefix-numeric-value current-prefix-arg))))

(defun eshell-printable-size (filesize &optional human-readable
                                       block-size use-colors)
  "Return a printable FILESIZE."
  (let ((size (float (or filesize 0))))
    (if human-readable
        (if (< size human-readable)
            (if (= (round size) 0)
                "0"
              (if block-size
                  "1.0k"
                (format "%.0f" size)))
          (setq size (/ size human-readable))
          (if (< size human-readable)
              (if (<= size 9.94)
                  (format "%.1fk" size)
                (format "%.0fk" size))
            (setq size (/ size human-readable))
            (if (< size human-readable)
                (let ((str (if (<= size 9.94)
                               (format "%.1fM" size)
                             (format "%.0fM" size))))
                  (if use-colors
                      (put-text-property 0 (length str)
                                         'face 'bold str))
                  str)
              (setq size (/ size human-readable))
              (if (< size human-readable)
                  (let ((str (if (<= size 9.94)
                                 (format "%.1fG" size)
                               (format "%.0fG" size))))
                    (if use-colors
                        (put-text-property 0 (length str)
                                           'face 'bold-italic str))
                    str)))))
      (if block-size
          (setq size (/ size block-size)))
      (format "%.0f" size))))

(defun eshell-winnow-list (entries exclude &optional predicates)
  "Pare down the ENTRIES list using the EXCLUDE regexp, and PREDICATES.
The original list is not affected.  If the result is only one element
long, it will be returned itself, rather than returning a one-element
list."
  (let ((flist (list t))
        valid p listified)
    (unless (listp entries)
      (setq entries (list entries)
            listified t))
    (dolist (entry entries)
      (unless (and exclude (string-match exclude entry))
        (setq p predicates valid (null p))
        (while p
          (if (funcall (car p) entry)
              (setq valid t)
            (setq p nil valid nil))
          (setq p (cdr p)))
        (when valid
          (nconc flist (list entry)))))
    (if listified
        (cadr flist)
      (cdr flist))))

(defsubst eshell-redisplay ()
  "Allow Emacs to redisplay buffers."
  ;; for some strange reason, Emacs 21 is prone to trigger an
  ;; "args out of range" error in `sit-for', if this function
  ;; runs while point is in the minibuffer and the users attempt
  ;; to use completion.  Don't ask me.
  (condition-case nil
      (sit-for 0 0)
    (error nil)))

(defun eshell-read-passwd-file (file)
  "Return an alist correlating gids to group names in FILE."
  (let (names)
    (when (file-readable-p file)
      (with-temp-buffer
        (insert-file-contents file)
        (goto-char (point-min))
        (while (not (eobp))
          (let* ((fields
                  (split-string (buffer-substring
                                 (point) (progn (end-of-line)
                                                (point))) ":")))
            (if (and (and fields (nth 0 fields) (nth 2 fields))
                     (not (assq (string-to-number (nth 2 fields)) names)))
                (setq names (cons (cons (string-to-number (nth 2 fields))
                                        (nth 0 fields))
                                  names))))
          (forward-line))))
    names))

(defun eshell-read-passwd (file result-var timestamp-var)
  "Read the contents of /etc/passwd for user names."
  (if (or (not (symbol-value result-var))
          (not (symbol-value timestamp-var))
          (time-less-p
           (symbol-value timestamp-var)
           (nth 5 (file-attributes file))))
      (progn
        (set result-var (eshell-read-passwd-file file))
        (set timestamp-var (current-time))))
  (symbol-value result-var))

(defun eshell-read-group-names ()
  "Read the contents of /etc/group for group names."
  (if eshell-group-file
      (eshell-read-passwd eshell-group-file 'eshell-group-names
                          'eshell-group-timestamp)))

(defsubst eshell-group-id (name)
  "Return the user id for user NAME."
  (car (rassoc name (eshell-read-group-names))))

(defsubst eshell-group-name (gid)
  "Return the group name for the given GID."
  (cdr (assoc gid (eshell-read-group-names))))

(defun eshell-read-user-names ()
  "Read the contents of /etc/passwd for user names."
  (if eshell-passwd-file
      (eshell-read-passwd eshell-passwd-file 'eshell-user-names
                          'eshell-user-timestamp)))

(defsubst eshell-user-id (name)
  "Return the user id for user NAME."
  (car (rassoc name (eshell-read-user-names))))

(defalias 'eshell-user-name 'user-login-name)

(defun eshell-read-hosts-file (filename)
  "Read in the hosts from FILENAME, default `eshell-hosts-file'."
  (let (hosts)
    (with-temp-buffer
      (insert-file-contents (or filename eshell-hosts-file))
      (goto-char (point-min))
      (while (re-search-forward
              "^\\([^#[:space:]]+\\)\\s-+\\(\\S-+\\)\\(\\s-*\\(\\S-+\\)\\)?" nil t)
        (if (match-string 1)
            (cl-pushnew (match-string 1) hosts :test #'equal))
        (if (match-string 2)
            (cl-pushnew (match-string 2) hosts :test #'equal))
        (if (match-string 4)
            (cl-pushnew (match-string 4) hosts :test #'equal))))
    (sort hosts #'string-lessp)))

(defun eshell-read-hosts (file result-var timestamp-var)
  "Read the contents of /etc/passwd for user names."
  (if (or (not (symbol-value result-var))
          (not (symbol-value timestamp-var))
          (time-less-p
           (symbol-value timestamp-var)
           (nth 5 (file-attributes file))))
      (progn
        (set result-var (eshell-read-hosts-file file))
        (set timestamp-var (current-time))))
  (symbol-value result-var))

(defun eshell-read-host-names ()
  "Read the contents of /etc/hosts for host names."
  (if eshell-hosts-file
      (eshell-read-hosts eshell-hosts-file 'eshell-host-names
                         'eshell-host-timestamp)))

(and (featurep 'xemacs)
     (not (fboundp 'subst-char-in-string))
     (defun subst-char-in-string (fromchar tochar string &optional inplace)
       "Replace FROMCHAR with TOCHAR in STRING each time it occurs.
Unless optional argument INPLACE is non-nil, return a new string."
       (let ((i (length string))
             (newstr (if inplace string (copy-sequence string))))
         (while (> i 0)
           (setq i (1- i))
           (if (eq (aref newstr i) fromchar)
               (aset newstr i tochar)))
         newstr)))

(defsubst eshell-copy-environment ()
  "Return an unrelated copy of `process-environment'."
  (mapcar 'concat process-environment))

(defun eshell-subgroups (groupsym)
  "Return all of the subgroups of GROUPSYM."
  (let ((subgroups (get groupsym 'custom-group))
        (subg (list t)))
    (while subgroups
      (if (eq (cadr (car subgroups)) 'custom-group)
          (nconc subg (list (caar subgroups))))
      (setq subgroups (cdr subgroups)))
    (cdr subg)))

(defmacro eshell-with-file-modes (modes &rest forms)
  "Evaluate, with file-modes set to MODES, the given FORMS."
  `(let ((modes (default-file-modes)))
     (set-default-file-modes ,modes)
     (unwind-protect
         (progn ,@forms)
       (set-default-file-modes modes))))

(defmacro eshell-with-private-file-modes (&rest forms)
  "Evaluate FORMS with private file modes set."
  `(eshell-with-file-modes ,eshell-private-file-modes ,@forms))

(defsubst eshell-make-private-directory (dir &optional parents)
  "Make DIR with file-modes set to `eshell-private-directory-modes'."
  (eshell-with-file-modes eshell-private-directory-modes
                          (make-directory dir parents)))

(defsubst eshell-substring (string sublen)
  "Return the beginning of STRING, up to SUBLEN bytes."
  (if string
      (if (> (length string) sublen)
          (substring string 0 sublen)
        string)))

(defvar ange-cache)

;; Partial reimplementation of Emacs's builtin directory-files-and-attributes.
;; id-format not implemented.
(and (featurep 'xemacs)
     (not (fboundp 'directory-files-and-attributes))
     (defun directory-files-and-attributes (directory &optional full match nosort _id-format)
    "Return a list of names of files and their attributes in DIRECTORY.
There are three optional arguments:
If FULL is non-nil, return absolute file names.  Otherwise return names
 that are relative to the specified directory.
If MATCH is non-nil, mention only file names that match the regexp MATCH.
If NOSORT is non-nil, the list is not sorted--its order is unpredictable.
 NOSORT is useful if you plan to sort the result yourself."
    (let ((directory (expand-file-name directory)) ange-cache)
      (mapcar
       (function
        (lambda (file)
          (cons file (eshell-file-attributes (expand-file-name file directory)))))
       (directory-files directory full match nosort)))))

(defun eshell-directory-files-and-attributes (dir &optional full match nosort id-format)
  "Make sure to use the handler for `directory-file-and-attributes'."
  (let* ((dir (expand-file-name dir)))
    (if (string-equal (file-remote-p dir 'method) "ftp")
        (let ((files (directory-files dir full match nosort)))
          (mapcar
           (lambda (file)
             (cons file (eshell-file-attributes (expand-file-name file dir))))
           files))
      (directory-files-and-attributes dir full match nosort id-format))))

(defun eshell-current-ange-uids ()
  (if (string-match "/\\([^@]+\\)@\\([^:]+\\):" default-directory)
      (let* ((host (match-string 2 default-directory))
             (user (match-string 1 default-directory))
             (host-users (assoc host eshell-ange-ls-uids)))
        (when host-users
          (setq host-users (cdr host-users))
          (cdr (assoc user host-users))))))

;; Add an autoload for parse-time-string
(if (and (not (fboundp 'parse-time-string))
         (locate-library "parse-time"))
    (autoload 'parse-time-string "parse-time"))

(eval-when-compile
  (require 'ange-ftp nil t))            ; ange-ftp-parse-filename

(defvar tramp-file-name-structure)
(declare-function ange-ftp-ls "ange-ftp"
                  (file lsargs parse &optional no-error wildcard))
(declare-function ange-ftp-file-modtime "ange-ftp" (file))

(defun eshell-parse-ange-ls (dir)
  (require 'ange-ftp)
  (require 'tramp)
  (let ((ange-ftp-name-format
         (list (nth 0 tramp-file-name-structure)
               (nth 3 tramp-file-name-structure)
               (nth 2 tramp-file-name-structure)
               (nth 4 tramp-file-name-structure)))
        ;; ange-ftp uses `ange-ftp-ftp-name-arg' and `ange-ftp-ftp-name-res'
        ;; for optimization in `ange-ftp-ftp-name'. If Tramp wasn't active,
        ;; there could be incorrect values from previous calls in case the
        ;; "ftp" method is used in the Tramp file name. So we unset
        ;; those values.
        (ange-ftp-ftp-name-arg "")
        (ange-ftp-ftp-name-res nil)
        entry)
    (with-temp-buffer
      (insert (ange-ftp-ls dir "-la" nil))
      (goto-char (point-min))
      (if (looking-at "^total [0-9]+$")
          (forward-line 1))
      ;; Some systems put in a blank line here.
      (if (eolp) (forward-line 1))
      (while (looking-at
              `,(concat "\\([dlscb-][rwxst-]+\\)"
                        "\\s-*" "\\([0-9]+\\)" "\\s-+"
                        "\\(\\S-+\\)" "\\s-+"
                        "\\(\\S-+\\)" "\\s-+"
                        "\\([0-9]+\\)" "\\s-+" "\\(.*\\)"))
        (let* ((perms (match-string 1))
               (links (string-to-number (match-string 2)))
               (user (match-string 3))
               (group (match-string 4))
               (size (string-to-number (match-string 5)))
               (name (ange-ftp-parse-filename))
               (mtime
                (if (fboundp 'parse-time-string)
                    (let ((moment (parse-time-string
                                   (match-string 6))))
                      (if (nth 0 moment)
                          (setcar (nthcdr 5 moment)
                                  (nth 5 (decode-time (current-time))))
                        (setcar (nthcdr 0 moment) 0)
                        (setcar (nthcdr 1 moment) 0)
                        (setcar (nthcdr 2 moment) 0))
                      (apply 'encode-time moment))
                  (ange-ftp-file-modtime (expand-file-name name dir))))
               symlink)
          (if (string-match "\\(.+\\) -> \\(.+\\)" name)
              (setq symlink (match-string 2 name)
                    name (match-string 1 name)))
          (setq entry
                (cons
                 (cons name
                       (list (if (eq (aref perms 0) ?d)
                                 t
                               symlink)
                             links user group
                             nil mtime nil
                             size perms nil nil)) entry)))
        (forward-line)))
    entry))

(defun eshell-file-attributes (file &optional id-format)
  "Return the attributes of FILE, playing tricks if it's over ange-ftp.
The optional argument ID-FORMAT specifies the preferred uid and
gid format.  Valid values are 'string and 'integer, defaulting to
'integer.  See `file-attributes'."
  (let* ((file (expand-file-name file))
         entry)
    (if (string-equal (file-remote-p file 'method) "ftp")
        (let ((base (file-name-nondirectory file))
              (dir (file-name-directory file)))
          (if (string-equal "" base) (setq base "."))
          (if (boundp 'ange-cache)
              (setq entry (cdr (assoc base (cdr (assoc dir ange-cache))))))
          (unless entry
            (setq entry (eshell-parse-ange-ls dir))
            (if (boundp 'ange-cache)
                (setq ange-cache
                      (cons (cons dir entry)
                            ange-cache)))
            (if entry
                (let ((fentry (assoc base (cdr entry))))
                  (if fentry
                      (setq entry (cdr fentry))
                    (setq entry nil)))))
          entry)
      (file-attributes file id-format))))

(defalias 'eshell-copy-tree 'copy-tree)

(defsubst eshell-processp (proc)
  "If the `processp' function does not exist, PROC is not a process."
  (and (fboundp 'processp) (processp proc)))

;; (defun eshell-copy-file
;;   (file newname &optional ok-if-already-exists keep-date)
;;   "Copy FILE to NEWNAME.  See docs for `copy-file'."
;;   (let (copied)
;;     (if (string-match "\\`\\([^:]+\\):\\(.*\\)" file)
;;       (let ((front (match-string 1 file))
;;             (back (match-string 2 file))
;;             buffer)
;;         (if (and front (string-match eshell-tar-regexp front)
;;                    (setq buffer (find-file-noselect front)))
;;           (with-current-buffer buffer
;;             (goto-char (point-min))
;;             (if (re-search-forward (concat " " (regexp-quote back)
;;                                            "$") nil t)
;;                 (progn
;;                   (tar-copy (if (file-directory-p newname)
;;                                 (expand-file-name
;;                                  (file-name-nondirectory back) newname)
;;                               newname))
;;                   (setq copied t))
;;               (error "%s not found in tar file %s" back front))))))
;;     (unless copied
;;       (copy-file file newname ok-if-already-exists keep-date))))

;; (defun eshell-file-attributes (filename)
;;   "Return a list of attributes of file FILENAME.
;; See the documentation for `file-attributes'."
;;   (let (result)
;;     (when (string-match "\\`\\([^:]+\\):\\(.*\\)\\'" filename)
;;       (let ((front (match-string 1 filename))
;;           (back (match-string 2 filename))
;;           buffer)
;;       (when (and front (string-match eshell-tar-regexp front)
;;                  (setq buffer (find-file-noselect front)))
;;         (with-current-buffer buffer
;;           (goto-char (point-min))
;;           (when (re-search-forward (concat " " (regexp-quote back)
;;                                            "\\s-*$") nil t)
;;             (let* ((descrip (tar-current-descriptor))
;;                    (tokens (tar-desc-tokens descrip)))
;;               (setq result
;;                     (list
;;                      (cond
;;                       ((eq (tar-header-link-type tokens) 5)
;;                        t)
;;                       ((eq (tar-header-link-type tokens) t)
;;                        (tar-header-link-name tokens)))
;;                      1
;;                      (tar-header-uid tokens)
;;                      (tar-header-gid tokens)
;;                      (tar-header-date tokens)
;;                      (tar-header-date tokens)
;;                      (tar-header-date tokens)
;;                      (tar-header-size tokens)
;;                      (concat
;;                       (cond
;;                        ((eq (tar-header-link-type tokens) 5) "d")
;;                        ((eq (tar-header-link-type tokens) t) "l")
;;                        (t "-"))
;;                       (tar-grind-file-mode (tar-header-mode tokens)
;;                                            (make-string 9 ? ) 0))
;;                      nil nil nil))))))))
;;     (or result
;;       (file-attributes filename))))

(provide 'esh-util)

(eval-when-compile (require 'cl-lib))

(require 'esh-util)
(require 'esh-mode)

(defgroup eshell nil
  "Command shell implemented entirely in Emacs Lisp.
It invokes no external processes beyond those requested by the
user, and is intended to be a functional replacement for command
shells such as bash, zsh, rc, 4dos."
  :link '(info-link "(eshell)Top")
  :version "21.1"
  :group 'applications)

;;;_* User Options
;;
;; The following user options modify the behavior of Eshell overall.
(defvar eshell-buffer-name)

(defun eshell-add-to-window-buffer-names ()
  "Add `eshell-buffer-name' to `same-window-buffer-names'."
  (declare (obsolete nil "24.3"))
  (add-to-list 'same-window-buffer-names eshell-buffer-name))

(defun eshell-remove-from-window-buffer-names ()
  "Remove `eshell-buffer-name' from `same-window-buffer-names'."
  (declare (obsolete nil "24.3"))
  (setq same-window-buffer-names
        (delete eshell-buffer-name same-window-buffer-names)))

(defcustom eshell-load-hook nil
  "A hook run once Eshell has been loaded."
  :type 'hook
  :group 'eshell)

(defcustom eshell-unload-hook '(eshell-unload-all-modules)
  "A hook run when Eshell is unloaded from memory."
  :type 'hook
  :group 'eshell)

(defcustom eshell-buffer-name "*eshell*"
  "The basename used for Eshell buffers."
  :type 'string
  :group 'eshell)

(defcustom eshell-directory-name
  (locate-user-emacs-file "eshell/" ".eshell/")
  "The directory where Eshell control files should be kept."
  :type 'directory
  :group 'eshell)

;;;_* Running Eshell
;;
;; There are only three commands used to invoke Eshell.  The first two
;; are intended for interactive use, while the third is meant for
;; programmers.  They are:

;;;###autoload
(defun eshell (&optional arg)
  "Create an interactive Eshell buffer.
The buffer used for Eshell sessions is determined by the value of
`eshell-buffer-name'.  If there is already an Eshell session active in
that buffer, Emacs will simply switch to it.  Otherwise, a new session
will begin.  A numeric prefix arg (as in `C-u 42 M-x eshell RET')
switches to the session with that number, creating it if necessary.  A
nonnumeric prefix arg means to create a new session.  Returns the
buffer selected (or created)."
  (interactive "P")
  (cl-assert eshell-buffer-name)
  (let ((buf (cond ((numberp arg)
                    (get-buffer-create (format "%s<%d>"
                                               eshell-buffer-name
                                               arg)))
                   (arg
                    (generate-new-buffer eshell-buffer-name))
                   (t
                    (get-buffer-create eshell-buffer-name)))))
    (cl-assert (and buf (buffer-live-p buf)))
    (pop-to-buffer-same-window buf)
    (unless (derived-mode-p 'eshell-mode)
      (eshell-mode))
    buf))

(defun eshell-return-exits-minibuffer ()
  (define-key eshell-mode-map [(control ?g)] 'abort-recursive-edit)
  (define-key eshell-mode-map [return] 'exit-minibuffer)
  (define-key eshell-mode-map [(control ?m)] 'exit-minibuffer)
  (define-key eshell-mode-map [(control ?j)] 'exit-minibuffer)
  (define-key eshell-mode-map [(meta return)] 'exit-minibuffer)
  (define-key eshell-mode-map [(meta control ?m)] 'exit-minibuffer))

(defvar eshell-non-interactive-p nil
  "A variable which is non-nil when Eshell is not running interactively.
Modules should use this variable so that they don't clutter
non-interactive sessions, such as when using `eshell-command'.")

(declare-function eshell-add-input-to-history "em-hist" (input))

;;;###autoload
(defun eshell-command (&optional command arg)
  "Execute the Eshell command string COMMAND.
With prefix ARG, insert output into the current buffer at point."
  (interactive)
  (require 'esh-cmd)
  (unless arg
    (setq arg current-prefix-arg))
  (let ((eshell-non-interactive-p t))
    ;; Enable `eshell-mode' only in this minibuffer.
    (minibuffer-with-setup-hook #'(lambda ()
                                    (eshell-mode)
                                    (eshell-return-exits-minibuffer))
      (unless command
        (setq command (read-from-minibuffer "Emacs shell command: "))
        (if (eshell-using-module 'eshell-hist)
            (eshell-add-input-to-history command)))))
  (unless command
    (error "No command specified!"))
  ;; redirection into the current buffer is achieved by adding an
  ;; output redirection to the end of the command, of the form
  ;; 'COMMAND >>> #<buffer BUFFER>'.  This will not interfere with
  ;; other redirections, since multiple redirections merely cause the
  ;; output to be copied to multiple target locations
  (if arg
      (setq command
            (concat command
                    (format " >>> #<buffer %s>"
                            (buffer-name (current-buffer))))))
  (save-excursion
    (let ((buf (set-buffer (generate-new-buffer " *eshell cmd*")))
          (eshell-non-interactive-p t))
      (eshell-mode)
      (let* ((proc (eshell-eval-command
                    (list 'eshell-commands
                          (eshell-parse-command command))))
             intr
             (bufname (if (and proc (listp proc))
                          "*EShell Async Command Output*"
                          (setq intr t)
                          "*EShell Command Output*")))
        (if (buffer-live-p (get-buffer bufname))
            (kill-buffer bufname))
        (rename-buffer bufname)
        ;; things get a little coarse here, since the desire is to
        ;; make the output as attractive as possible, with no
        ;; extraneous newlines
        (when intr
          (if (eshell-interactive-process)
              (eshell-wait-for-process (eshell-interactive-process)))
          (cl-assert (not (eshell-interactive-process)))
          (goto-char (point-max))
          (while (and (bolp) (not (bobp)))
            (delete-char -1)))
        (cl-assert (and buf (buffer-live-p buf)))
        (unless arg
          (let ((len (if (not intr) 2
                         (count-lines (point-min) (point-max)))))
            (cond
              ((= len 0)
               (message "(There was no command output)")
               (kill-buffer buf))
              ((= len 1)
               (message "%s" (buffer-string))
               (kill-buffer buf))
              (t
               (save-selected-window
                 (select-window (display-buffer buf))
                 (goto-char (point-min))
                 ;; cause the output buffer to take up as little screen
                 ;; real-estate as possible, if temp buffer resizing is
                 ;; enabled
                 (and intr temp-buffer-resize-mode
                      (resize-temp-buffer-window)))))))))))

;;;###autoload
(defun eshell-command-result (command &optional status-var)
  "Execute the given Eshell COMMAND, and return the result.
The result might be any Lisp object.
If STATUS-VAR is a symbol, it will be set to the exit status of the
command.  This is the only way to determine whether the value returned
corresponding to a successful execution."
  ;; a null command produces a null, successful result
  (if (not command)
      (ignore
       (if (and status-var (symbolp status-var))
           (set status-var 0)))
    (with-temp-buffer
      (let ((eshell-non-interactive-p t))
        (eshell-mode)
        (let ((result (eshell-do-eval
                       (list 'eshell-commands
                             (list 'eshell-command-to-value
                                   (eshell-parse-command command))) t)))
          (cl-assert (eq (car result) 'quote))
          (if (and status-var (symbolp status-var))
              (set status-var eshell-last-command-status))
          (cadr result))))))

;;;_* Reporting bugs
;;
;; If you do encounter a bug, on any system, please report
;; it -- in addition to any particular oddities in your configuration
;; -- so that the problem may be corrected for the benefit of others.

;;;###autoload
(define-obsolete-function-alias 'eshell-report-bug 'report-emacs-bug "23.1")

;;; Code:

(defun eshell-unload-all-modules ()
  "Unload all modules that were loaded by Eshell, if possible.
If the user has require'd in any of the modules, or customized a
variable with a :require tag (such as `eshell-prefer-to-shell'), it
will be impossible to unload Eshell completely without restarting
Emacs."
  ;; if the user set `eshell-prefer-to-shell' to t, but never loaded
  ;; Eshell, then `eshell-subgroups' will be unbound
  (when (fboundp 'eshell-subgroups)
    (dolist (module (eshell-subgroups 'eshell))
      ;; this really only unloads as many modules as possible,
      ;; since other `require' references (such as by customizing
      ;; `eshell-prefer-to-shell' to a non-nil value) might make it
      ;; impossible to unload Eshell completely
      (if (featurep module)
          (ignore-errors
            (message "Unloading %s..." (symbol-name module))
            (unload-feature module)
            (message "Unloading %s...done" (symbol-name module)))))
    (message "Unloading eshell...done")))

(run-hooks 'eshell-load-hook)

(provide 'eshell)

(provide 'esh-module)

(require 'eshell)
(require 'esh-util)

(defgroup eshell-module nil
  "The `eshell-module' group is for Eshell extension modules, which
provide optional behavior which the user can enable or disable by
customizing the variable `eshell-modules-list'."
  :tag "Extension modules"
  :group 'eshell)

;; load the defgroup's for the standard extension modules, so that
;; documentation can be provided when the user customize's
;; `eshell-modules-list'.  We use "(progn (defgroup ..." in each file
;; to force the autoloader into including the entire defgroup, rather
;; than an abbreviated version.
(load "esh-groups" nil 'nomessage)

;;; User Variables:

(defcustom eshell-module-unload-hook
  '(eshell-unload-extension-modules)
  "A hook run when `eshell-module' is unloaded."
  :type 'hook
  :group 'eshell-module)

(defcustom eshell-modules-list
  '(eshell-alias
    eshell-banner
    eshell-basic
    eshell-cmpl
    eshell-dirs
    eshell-glob
    eshell-hist
    eshell-ls
    eshell-pred
    eshell-prompt
    eshell-script
    eshell-term
    eshell-unix)
  "A list of optional add-on modules to be loaded by Eshell.
Changes will only take effect in future Eshell buffers."
  :type (append
         (list 'set ':tag "Supported modules")
         (mapcar
          (function
           (lambda (modname)
             (let ((modsym (intern modname)))
               (list 'const
                     ':tag (format "%s -- %s" modname
                                   (get modsym 'custom-tag))
                     ':link (caar (get modsym 'custom-links))
                     ':doc (concat "\n" (get modsym 'group-documentation)
                                   "\n ")
                     modsym))))
          (sort (mapcar 'symbol-name
                        (eshell-subgroups 'eshell-module))
                'string-lessp))
         '((repeat :inline t :tag "Other modules" symbol)))
  :group 'eshell-module)

;;; Code:

(defsubst eshell-using-module (module)
  "Return non-nil if a certain Eshell MODULE is in use.
The MODULE should be a symbol corresponding to that module's
customization group.  Example: `eshell-cmpl' for that module."
  (memq module eshell-modules-list))

(defun eshell-unload-extension-modules ()
  "Unload any memory resident extension modules."
  (dolist (module (eshell-subgroups 'eshell-module))
    (if (featurep module)
        (ignore-errors
          (message "Unloading %s..." (symbol-name module))
          (unload-feature module)
          (message "Unloading %s...done" (symbol-name module))))))

(provide 'esh-var)

(require 'esh-util)
(require 'esh-cmd)
(require 'esh-opt)

(require 'pcomplete)
(require 'env)
(require 'ring)

(defgroup eshell-var nil
  "Variable interpolation is introduced whenever the '$' character
appears unquoted in any argument (except when that argument is
surrounded by single quotes).  It may be used to interpolate a
variable value, a subcommand, or even the result of a Lisp form."
  :tag "Variable handling"
  :group 'eshell)

;;; User Variables:

(defcustom eshell-var-load-hook nil
  "A list of functions to call when loading `eshell-var'."
  :version "24.1"                       ; removed eshell-var-initialize
  :type 'hook
  :group 'eshell-var)

(defcustom eshell-prefer-lisp-variables nil
  "If non-nil, prefer Lisp variables to environment variables."
  :type 'boolean
  :group 'eshell-var)

(defcustom eshell-complete-export-definition t
  "If non-nil, completing names for `export' shows current definition."
  :type 'boolean
  :group 'eshell-var)

(defcustom eshell-modify-global-environment nil
  "If non-nil, using `export' changes Emacs's global environment."
  :type 'boolean
  :group 'eshell-var)

(defcustom eshell-variable-name-regexp "[A-Za-z0-9_-]+"
  "A regexp identifying what constitutes a variable name reference.
Note that this only applies for '$NAME'.  If the syntax '$<NAME>' is
used, then NAME can contain any character, including angle brackets,
if they are quoted with a backslash."
  :type 'regexp
  :group 'eshell-var)

(defcustom eshell-variable-aliases-list
  '(;; for eshell.el
    ("COLUMNS" (lambda (indices) (window-width)) t)
    ("LINES" (lambda (indices) (window-height)) t)

    ;; for eshell-cmd.el
    ("_" (lambda (indices)
           (if (not indices)
               (car (last eshell-last-arguments))
             (eshell-apply-indices eshell-last-arguments
                                   indices))))
    ("?" eshell-last-command-status)
    ("$" eshell-last-command-result)
    ("0" eshell-command-name)
    ("1" (lambda (indices) (nth 0 eshell-command-arguments)))
    ("2" (lambda (indices) (nth 1 eshell-command-arguments)))
    ("3" (lambda (indices) (nth 2 eshell-command-arguments)))
    ("4" (lambda (indices) (nth 3 eshell-command-arguments)))
    ("5" (lambda (indices) (nth 4 eshell-command-arguments)))
    ("6" (lambda (indices) (nth 5 eshell-command-arguments)))
    ("7" (lambda (indices) (nth 6 eshell-command-arguments)))
    ("8" (lambda (indices) (nth 7 eshell-command-arguments)))
    ("9" (lambda (indices) (nth 8 eshell-command-arguments)))
    ("*" (lambda (indices)
           (if (not indices)
               eshell-command-arguments
             (eshell-apply-indices eshell-command-arguments
                                   indices)))))
  "This list provides aliasing for variable references.
It is very similar in concept to what `eshell-user-aliases-list' does
for commands.  Each member of this defines the name of a command,
and the Lisp value to return for that variable if it is accessed
via the syntax '$NAME'.

If the value is a function, that function will be called with two
arguments: the list of the indices that was used in the reference, and
whether the user is requesting the length of the ultimate element.
For example, a reference of '$NAME[10][20]' would result in the
function for alias `NAME' being called (assuming it were aliased to a
function), and the arguments passed to this function would be the list
'(10 20)', and nil."
  :type '(repeat (list string sexp
                       (choice (const :tag "Copy to environment" t)
                               (const :tag "Use only in Eshell" nil))))
  :group 'eshell-var)

(put 'eshell-variable-aliases-list 'risky-local-variable t)

;;; Functions:

(defun eshell-var-initialize ()
  "Initialize the variable handle code."
  ;; Break the association with our parent's environment.  Otherwise,
  ;; changing a variable will affect all of Emacs.
  (unless eshell-modify-global-environment
    (set (make-local-variable 'process-environment)
         (eshell-copy-environment)))

  (define-key eshell-command-map [(meta ?v)] 'eshell-insert-envvar)

  (set (make-local-variable 'eshell-special-chars-inside-quoting)
       (append eshell-special-chars-inside-quoting '(?$)))
  (set (make-local-variable 'eshell-special-chars-outside-quoting)
       (append eshell-special-chars-outside-quoting '(?$)))

  (add-hook 'eshell-parse-argument-hook 'eshell-interpolate-variable t t)

  (add-hook 'eshell-prepare-command-hook
            'eshell-handle-local-variables nil t)

  (when (eshell-using-module 'eshell-cmpl)
    (add-hook 'pcomplete-try-first-hook
              'eshell-complete-variable-reference nil t)
    (add-hook 'pcomplete-try-first-hook
              'eshell-complete-variable-assignment nil t)))

(defun eshell-handle-local-variables ()
  "Allow for the syntax 'VAR=val <command> <args>'."
  ;; strip off any null commands, which can only happen if a variable
  ;; evaluates to nil, such as "$var x", where `var' is nil.  The
  ;; command name in that case becomes `x', for compatibility with
  ;; most regular shells (the difference is that they do an
  ;; interpolation pass before the argument parsing pass, but Eshell
  ;; does both at the same time).
  (while (and (not eshell-last-command-name)
              eshell-last-arguments)
    (setq eshell-last-command-name (car eshell-last-arguments)
          eshell-last-arguments (cdr eshell-last-arguments)))
  (let ((setvar "\\`\\([A-Za-z_][A-Za-z0-9_]*\\)=\\(.*\\)\\'")
        (command (eshell-stringify eshell-last-command-name))
        (args eshell-last-arguments))
    ;; local variable settings (such as 'CFLAGS=-O2 make') are handled
    ;; by making the whole command into a subcommand, and calling
    ;; setenv immediately before the command is invoked.  This means
    ;; that 'BLAH=x cd blah' won't work exactly as expected, but that
    ;; is by no means a typical use of local environment variables.
    (if (and command (string-match setvar command))
        (throw
         'eshell-replace-command
         (list
          'eshell-as-subcommand
          (append
           (list 'progn)
           (let ((l (list t)))
             (while (string-match setvar command)
               (nconc
                l (list
                   (list 'setenv (match-string 1 command)
                         (match-string 2 command)
                         (= (length (match-string 2 command)) 0))))
               (setq command (eshell-stringify (car args))
                     args (cdr args)))
             (cdr l))
           (list (list 'eshell-named-command
                       command (list 'quote args)))))))))

(defun eshell-interpolate-variable ()
  "Parse a variable interpolation.
This function is explicit for adding to `eshell-parse-argument-hook'."
  (when (and (eq (char-after) ?$)
             (/= (1+ (point)) (point-max)))
    (forward-char)
    (list 'eshell-escape-arg
          (eshell-parse-variable))))

(defun eshell/define (var-alias definition)
  "Define a VAR-ALIAS using DEFINITION."
  (if (not definition)
      (setq eshell-variable-aliases-list
            (delq (assoc var-alias eshell-variable-aliases-list)
                  eshell-variable-aliases-list))
    (let ((def (assoc var-alias eshell-variable-aliases-list))
          (alias-def
           (list var-alias
                 (list 'quote (if (= (length definition) 1)
                                  (car definition)
                                definition)))))
      (if def
          (setq eshell-variable-aliases-list
                (delq (assoc var-alias eshell-variable-aliases-list)
                      eshell-variable-aliases-list)))
      (setq eshell-variable-aliases-list
            (cons alias-def
                  eshell-variable-aliases-list))))
  nil)

(defun eshell/export (&rest sets)
  "This alias allows the `export' command to act as bash users expect."
  (while sets
    (if (and (stringp (car sets))
             (string-match "^\\([^=]+\\)=\\(.*\\)" (car sets)))
        (setenv (match-string 1 (car sets))
                (match-string 2 (car sets))))
    (setq sets (cdr sets))))

(defun pcomplete/eshell-mode/export ()
  "Completion function for Eshell's `export'."
  (while (pcomplete-here
          (if eshell-complete-export-definition
              process-environment
            (eshell-envvar-names)))))

(defun eshell/unset (&rest args)
  "Unset an environment variable."
  (while args
    (if (stringp (car args))
        (setenv (car args) nil t))
    (setq args (cdr args))))

(defun pcomplete/eshell-mode/unset ()
  "Completion function for Eshell's `unset'."
  (while (pcomplete-here (eshell-envvar-names))))

(defun eshell/setq (&rest args)
  "Allow command-ish use of `setq'."
  (let (last-value)
    (while args
      (let ((sym (intern (car args)))
            (val (cadr args)))
        (setq last-value (set sym val)
              args (cddr args))))
    last-value))

(defun pcomplete/eshell-mode/setq ()
  "Completion function for Eshell's `setq'."
  (while (and (pcomplete-here (all-completions pcomplete-stub
                                               obarray 'boundp))
              (pcomplete-here))))

(defun eshell/env (&rest args)
  "Implementation of `env' in Lisp."
  (eshell-init-print-buffer)
  (eshell-eval-using-options
   "env" args
   '((?h "help" nil nil "show this usage screen")
     :external "env"
     :usage "<no arguments>")
   (dolist (setting (sort (eshell-environment-variables) 'string-lessp))
     (eshell-buffered-print setting "\n"))
   (eshell-flush)))

(defun eshell-insert-envvar (envvar-name)
  "Insert ENVVAR-NAME into the current buffer at point."
  (interactive
   (list (read-envvar-name "Name of environment variable: " t)))
  (insert-and-inherit "$" envvar-name))

(defun eshell-envvar-names (&optional environment)
  "Return a list of currently visible environment variable names."
  (mapcar (function
           (lambda (x)
             (substring x 0 (string-match "=" x))))
          (or environment process-environment)))

(defun eshell-environment-variables ()
  "Return a `process-environment', fully updated.
This involves setting any variable aliases which affect the
environment, as specified in `eshell-variable-aliases-list'."
  (let ((process-environment (eshell-copy-environment)))
    (dolist (var-alias eshell-variable-aliases-list)
      (if (nth 2 var-alias)
          (setenv (car var-alias)
                  (eshell-stringify
                   (or (eshell-get-variable (car var-alias)) "")))))
    process-environment))

(defun eshell-parse-variable ()
  "Parse the next variable reference at point.
The variable name could refer to either an environment variable, or a
Lisp variable.  The priority order depends on the setting of
`eshell-prefer-lisp-variables'.

Its purpose is to call `eshell-parse-variable-ref', and then to
process any indices that come after the variable reference."
  (let* ((get-len (when (eq (char-after) ?#)
                    (forward-char) t))
         value indices)
    (setq value (eshell-parse-variable-ref)
          indices (and (not (eobp))
                       (eq (char-after) ?\[)
                       (eshell-parse-indices))
          value `(let ((indices ',indices)) ,value))
    (if get-len
        `(length ,value)
      value)))

(defun eshell-parse-variable-ref ()
  "Eval a variable reference.
Returns a Lisp form which, if evaluated, will return the value of the
variable.

Possible options are:

  NAME          an environment or Lisp variable value
  <LONG-NAME>   disambiguates the length of the name
  {COMMAND}     result of command is variable's value
  (LISP-FORM)   result of Lisp form is variable's value"
  (cond
   ((eq (char-after) ?{)
    (let ((end (eshell-find-delimiter ?\{ ?\})))
      (if (not end)
          (throw 'eshell-incomplete ?\{)
        (prog1
            (list 'eshell-convert
                  (list 'eshell-command-to-value
                        (list 'eshell-as-subcommand
                              (eshell-parse-command
                               (cons (1+ (point)) end)))))
          (goto-char (1+ end))))))
   ((memq (char-after) '(?\' ?\"))
    (let ((name (if (eq (char-after) ?\')
                    (eshell-parse-literal-quote)
                  (eshell-parse-double-quote))))
      (if name
          (list 'eshell-get-variable (eval name) 'indices))))
   ((eq (char-after) ?\<)
    (let ((end (eshell-find-delimiter ?\< ?\>)))
      (if (not end)
          (throw 'eshell-incomplete ?\<)
        (let* ((temp (make-temp-file temporary-file-directory))
               (cmd (concat (buffer-substring (1+ (point)) end)
                            " > " temp)))
          (prog1
              (list
               'let (list (list 'eshell-current-handles
                                (list 'eshell-create-handles temp
                                      (list 'quote 'overwrite))))
               (list
                'progn
                (list 'eshell-as-subcommand
                      (eshell-parse-command cmd))
                (list 'ignore
                      (list 'nconc 'eshell-this-command-hook
                            (list 'list
                                  (list 'function
                                        (list 'lambda nil
                                              (list 'delete-file temp))))))
                (list 'quote temp)))
            (goto-char (1+ end)))))))
   ((eq (char-after) ?\()
    (condition-case nil
        (list 'eshell-command-to-value
              (list 'eshell-lisp-command
                    (list 'quote (read (current-buffer)))))
      (end-of-file
       (throw 'eshell-incomplete ?\())))
   ((assoc (char-to-string (char-after))
           eshell-variable-aliases-list)
    (forward-char)
    (list 'eshell-get-variable
          (char-to-string (char-before)) 'indices))
   ((looking-at eshell-variable-name-regexp)
    (prog1
        (list 'eshell-get-variable (match-string 0) 'indices)
      (goto-char (match-end 0))))
   (t
    (error "Invalid variable reference"))))

(defvar eshell-glob-function)

(defun eshell-parse-indices ()
  "Parse and return a list of list of indices."
  (let (indices)
    (while (eq (char-after) ?\[)
      (let ((end (eshell-find-delimiter ?\[ ?\])))
        (if (not end)
            (throw 'eshell-incomplete ?\[)
          (forward-char)
          (let (eshell-glob-function)
            (setq indices (cons (eshell-parse-arguments (point) end)
                                indices)))
          (goto-char (1+ end)))))
    (nreverse indices)))

(defun eshell-get-variable (name &optional indices)
  "Get the value for the variable NAME."
  (let* ((alias (assoc name eshell-variable-aliases-list))
         (var (if alias
                  (cadr alias)
                name)))
    (if (and alias (functionp var))
        (funcall var indices)
      (eshell-apply-indices
       (cond
        ((stringp var)
         (let ((sym (intern-soft var)))
           (if (and sym (boundp sym)
                    (or eshell-prefer-lisp-variables
                        (memq sym eshell--local-vars) ; bug#15372
                        (not (getenv var))))
               (symbol-value sym)
             (getenv var))))
        ((symbolp var)
         (symbol-value var))
        (t
         (error "Unknown variable `%s'" (eshell-stringify var))))
       indices))))

(defun eshell-apply-indices (value indices)
  "Apply to VALUE all of the given INDICES, returning the sub-result.
The format of INDICES is:

  ((INT-OR-NAME-OR-OTHER INT-OR-NAME INT-OR-NAME ...)
   ...)

Each member of INDICES represents a level of nesting.  If the first
member of a sublist is not an integer or name, and the value it's
reference is a string, that will be used as the regexp with which is
to divide the string into sub-parts.  The default is whitespace.
Otherwise, each INT-OR-NAME refers to an element of the list value.
Integers imply a direct index, and names, an associate lookup using
`assoc'.

For example, to retrieve the second element of a user's record in
'/etc/passwd', the variable reference would look like:

  ${egrep johnw /etc/passwd}[: 2]"
  (while indices
    (let ((refs (car indices)))
      (when (stringp value)
        (let (separator)
          (if (not (or (not (stringp (caar indices)))
                       (string-match
                        (concat "^" eshell-variable-name-regexp "$")
                        (caar indices))))
              (setq separator (caar indices)
                    refs (cdr refs)))
          (setq value
                (mapcar 'eshell-convert
                        (split-string value separator)))))
      (cond
       ((< (length refs) 0)
        (error "Invalid array variable index: %s"
               (eshell-stringify refs)))
       ((= (length refs) 1)
        (setq value (eshell-index-value value (car refs))))
       (t
        (let ((new-value (list t)))
          (while refs
            (nconc new-value
                   (list (eshell-index-value value
                                             (car refs))))
            (setq refs (cdr refs)))
          (setq value (cdr new-value))))))
    (setq indices (cdr indices)))
  value)

(defun eshell-index-value (value index)
  "Reference VALUE using the given INDEX."
  (if (stringp index)
      (cdr (assoc index value))
    (cond
     ((ring-p value)
      (if (> index (ring-length value))
          (error "Index exceeds length of ring")
        (ring-ref value index)))
     ((listp value)
      (if (> index (length value))
          (error "Index exceeds length of list")
        (nth index value)))
     ((vectorp value)
      (if (> index (length value))
          (error "Index exceeds length of vector")
        (aref value index)))
     (t
      (error "Invalid data type for indexing")))))

;;;_* Variable name completion

(defun eshell-complete-variable-reference ()
  "If there is a variable reference, complete it."
  (let ((arg (pcomplete-actual-arg)) index)
    (when (setq index
                (string-match
                 (concat "\\$\\(" eshell-variable-name-regexp
                         "\\)?\\'") arg))
      (setq pcomplete-stub (substring arg (1+ index)))
      (throw 'pcomplete-completions (eshell-variables-list)))))

(defun eshell-variables-list ()
  "Generate list of applicable variables."
  (let ((argname pcomplete-stub)
        completions)
    (dolist (alias eshell-variable-aliases-list)
      (if (string-match (concat "^" argname) (car alias))
          (setq completions (cons (car alias) completions))))
    (sort
     (append
      (mapcar
       (function
        (lambda (varname)
          (let ((value (eshell-get-variable varname)))
            (if (and value
                     (stringp value)
                     (file-directory-p value))
                (concat varname "/")
              varname))))
       (eshell-envvar-names (eshell-environment-variables)))
      (all-completions argname obarray 'boundp)
      completions)
     'string-lessp)))

(defun eshell-complete-variable-assignment ()
  "If there is a variable assignment, allow completion of entries."
  (let ((arg (pcomplete-actual-arg)) pos)
    (when (string-match (concat "\\`" eshell-variable-name-regexp "=") arg)
      (setq pos (match-end 0))
      (if (string-match "\\(:\\)[^:]*\\'" arg)
          (setq pos (match-end 1)))
      (setq pcomplete-stub (substring arg pos))
      (throw 'pcomplete-completions (pcomplete-entries)))))

(provide 'esh-proc)

(require 'esh-cmd)

(defgroup eshell-proc nil
  "When Eshell invokes external commands, it always does so
asynchronously, so that Emacs isn't tied up waiting for the process to
finish."
  :tag "Process management"
  :group 'eshell)

;;; User Variables:

(defcustom eshell-proc-load-hook nil
  "A hook that gets run when `eshell-proc' is loaded."
  :version "24.1"                       ; removed eshell-proc-initialize
  :type 'hook
  :group 'eshell-proc)

(defcustom eshell-process-wait-seconds 0
  "The number of seconds to delay waiting for a synchronous process."
  :type 'integer
  :group 'eshell-proc)

(defcustom eshell-process-wait-milliseconds 50
  "The number of milliseconds to delay waiting for a synchronous process."
  :type 'integer
  :group 'eshell-proc)

(defcustom eshell-done-messages-in-minibuffer t
  "If non-nil, subjob \"Done\" messages will display in minibuffer."
  :type 'boolean
  :group 'eshell-proc)

(defcustom eshell-delete-exited-processes t
  "If nil, process entries will stick around until `jobs' is run.
This variable sets the buffer-local value of `delete-exited-processes'
in Eshell buffers.

This variable causes Eshell to mimic the behavior of bash when set to
nil.  It allows the user to view the exit status of a completed subjob
\(process) at their leisure, because the process entry remains in
memory until the user examines it using \\[list-processes].

Otherwise, if `eshell-done-messages-in-minibuffer' is nil, and this
variable is set to t, the only indication the user will have that a
subjob is done is that it will no longer appear in the
\\[list-processes\\] display.

Note that Eshell will have to be restarted for a change in this
variable's value to take effect."
  :type 'boolean
  :group 'eshell-proc)

(defcustom eshell-reset-signals
  "^\\(interrupt\\|killed\\|quit\\|stopped\\)"
  "If a termination signal matches this regexp, the terminal will be reset."
  :type 'regexp
  :group 'eshell-proc)

(defcustom eshell-exec-hook nil
  "Called each time a process is exec'd by `eshell-gather-process-output'.
It is passed one argument, which is the process that was just started.
It is useful for things that must be done each time a process is
executed in a eshell mode buffer (e.g., `process-kill-without-query').
In contrast, `eshell-mode-hook' is only executed once when the buffer
is created."
  :type 'hook
  :group 'eshell-proc)

(defcustom eshell-kill-hook nil
  "Called when a process run by `eshell-gather-process-output' has ended.
It is passed two arguments: the process that was just ended, and the
termination status (as a string).  Note that the first argument may be
nil, in which case the user attempted to send a signal, but there was
no relevant process.  This can be used for displaying help
information, for example."
  :version "24.1"                       ; removed eshell-reset-after-proc
  :type 'hook
  :group 'eshell-proc)

;;; Internal Variables:

(defvar eshell-current-subjob-p nil)

(defvar eshell-process-list nil
  "A list of the current status of subprocesses.")

;;; Functions:

(defun eshell-kill-process-function (proc status)
  "Function run when killing a process.
Runs `eshell-reset-after-proc' and `eshell-kill-hook', passing arguments
PROC and STATUS to functions on the latter."
  ;; Was there till 24.1, but it is not optional.
  (if (memq 'eshell-reset-after-proc eshell-kill-hook)
      (setq eshell-kill-hook (delq 'eshell-reset-after-proc eshell-kill-hook)))
  (eshell-reset-after-proc status)
  (run-hook-with-args 'eshell-kill-hook proc status))

(defun eshell-proc-initialize ()
  "Initialize the process handling code."
  (make-local-variable 'eshell-process-list)
  (define-key eshell-command-map [(meta ?i)] 'eshell-insert-process)
  (define-key eshell-command-map [(control ?c)]  'eshell-interrupt-process)
  (define-key eshell-command-map [(control ?k)]  'eshell-kill-process)
  (define-key eshell-command-map [(control ?d)]  'eshell-send-eof-to-process)
; (define-key eshell-command-map [(control ?q)]  'eshell-continue-process)
  (define-key eshell-command-map [(control ?s)]  'list-processes)
; (define-key eshell-command-map [(control ?z)]  'eshell-stop-process)
  (define-key eshell-command-map [(control ?\\)] 'eshell-quit-process))

(defun eshell-reset-after-proc (status)
  "Reset the command input location after a process terminates.
The signals which will cause this to happen are matched by
`eshell-reset-signals'."
  (if (and (stringp status)
           (string-match eshell-reset-signals status))
      (eshell-reset)))

(defun eshell-wait-for-process (&rest procs)
  "Wait until PROC has successfully completed."
  (while procs
    (let ((proc (car procs)))
      (when (eshell-processp proc)
        ;; NYI: If the process gets stopped here, that's bad.
        (while (assq proc eshell-process-list)
          (if (input-pending-p)
              (discard-input))
          (sit-for eshell-process-wait-seconds
                   eshell-process-wait-milliseconds))))
    (setq procs (cdr procs))))

(defalias 'eshell/wait 'eshell-wait-for-process)

(defun eshell/jobs (&rest args)
  "List processes, if there are any."
  (and (fboundp 'process-list)
       (process-list)
       (list-processes)))

(defun eshell/kill (&rest args)
  "Kill processes.
Usage: kill [-<signal>] <pid>|<process> ...
Accepts PIDs and process objects."
  ;; If the first argument starts with a dash, treat it as the signal
  ;; specifier.
  (let ((signum 'SIGINT))
    (let ((arg (car args))
          (case-fold-search nil))
      (when (stringp arg)
        (cond
         ((string-match "\\`-[[:digit:]]+\\'" arg)
          (setq signum (abs (string-to-number arg))))
         ((string-match "\\`-\\([[:upper:]]+\\|[[:lower:]]+\\)\\'" arg)
          (setq signum (abs (string-to-number arg)))))
        (setq args (cdr args))))
    (while args
      (let ((arg (if (eshell-processp (car args))
                     (process-id (car args))
                   (car args))))
        (when arg
          (cond
           ((null arg)
            (error "kill: null pid.  Process may actually be a network connection."))
           ((not (numberp arg))
            (error "kill: invalid argument type: %s" (type-of arg)))
           ((and (numberp arg)
                 (<= arg 0))
            (error "kill: bad pid: %d" arg))
           (t
            (signal-process arg signum)))))
      (setq args (cdr args))))
  nil)

(defun eshell-read-process-name (prompt)
  "Read the name of a process from the minibuffer, using completion.
The prompt will be set to PROMPT."
  (completing-read prompt
                   (mapcar
                    (function
                     (lambda (proc)
                       (cons (process-name proc) t)))
                    (process-list)) nil t))

(defun eshell-insert-process (process)
  "Insert the name of PROCESS into the current buffer at point."
  (interactive
   (list (get-process
          (eshell-read-process-name "Name of process: "))))
  (insert-and-inherit "#<process " (process-name process) ">"))

(defsubst eshell-record-process-object (object)
  "Record OBJECT as now running."
  (if (and (eshell-processp object)
           eshell-current-subjob-p)
      (eshell-interactive-print
       (format "[%s] %d\n" (process-name object) (process-id object))))
  (setq eshell-process-list
        (cons (list object eshell-current-handles
                    eshell-current-subjob-p nil nil)
              eshell-process-list)))

(defun eshell-remove-process-entry (entry)
  "Record the process ENTRY as fully completed."
  (if (and (eshell-processp (car entry))
           (nth 2 entry)
           eshell-done-messages-in-minibuffer)
      (message "[%s]+ Done %s" (process-name (car entry))
               (process-command (car entry))))
  (setq eshell-process-list
        (delq entry eshell-process-list)))

(defvar eshell-scratch-buffer " *eshell-scratch*"
  "Scratch buffer for holding Eshell's input/output.")
(defvar eshell-last-sync-output-start nil
  "A marker that tracks the beginning of output of the last subprocess.
Used only on systems which do not support async subprocesses.")

(defvar eshell-needs-pipe '("bc")
  "List of commands which need `process-connection-type' to be nil.
Currently only affects commands in pipelines, and not those at
the front.  If an element contains a directory part it must match
the full name of a command, otherwise just the nondirectory part must match.")

(defun eshell-needs-pipe-p (command)
  "Return non-nil if COMMAND needs `process-connection-type' to be nil.
See `eshell-needs-pipe'."
  (and eshell-in-pipeline-p
       (not (eq eshell-in-pipeline-p 'first))
       ;; FIXME should this return non-nil for anything that is
       ;; neither 'first nor 'last?  See bug#1388 discussion.
       (catch 'found
         (dolist (exe eshell-needs-pipe)
           (if (string-equal exe (if (string-match "/" exe)
                                     command
                                   (file-name-nondirectory command)))
               (throw 'found t))))))

(defun eshell-gather-process-output (command args)
  "Gather the output from COMMAND + ARGS."
  (unless (and (file-executable-p command)
               (file-regular-p (file-truename command)))
    (error "%s: not an executable file" command))
  (let* ((delete-exited-processes
          (if eshell-current-subjob-p
              eshell-delete-exited-processes
            delete-exited-processes))
         (process-environment (eshell-environment-variables))
         proc decoding encoding changed)
    (cond
     ((fboundp 'start-file-process)
      (setq proc
            (let ((process-connection-type
                   (unless (eshell-needs-pipe-p command)
                     process-connection-type))
                  (command (or (file-remote-p command 'localname) command)))
              (apply 'start-file-process
                     (file-name-nondirectory command) nil
                     ;; `start-process' can't deal with relative filenames.
                     (append (list (expand-file-name command)) args))))
      (eshell-record-process-object proc)
      (set-process-buffer proc (current-buffer))
      (if (eshell-interactive-output-p)
          (set-process-filter proc 'eshell-output-filter)
        (set-process-filter proc 'eshell-insertion-filter))
      (set-process-sentinel proc 'eshell-sentinel)
      (run-hook-with-args 'eshell-exec-hook proc)
      (when (fboundp 'process-coding-system)
        (let ((coding-systems (process-coding-system proc)))
          (setq decoding (car coding-systems)
                encoding (cdr coding-systems)))
        ;; If start-process decided to use some coding system for
        ;; decoding data sent from the process and the coding system
        ;; doesn't specify EOL conversion, we had better convert CRLF
        ;; to LF.
        (if (vectorp (coding-system-eol-type decoding))
            (setq decoding (coding-system-change-eol-conversion decoding 'dos)
                  changed t))
        ;; Even if start-process left the coding system for encoding
        ;; data sent from the process undecided, we had better use the
        ;; same one as what we use for decoding.  But, we should
        ;; suppress EOL conversion.
        (if (and decoding (not encoding))
            (setq encoding (coding-system-change-eol-conversion decoding 'unix)
                  changed t))
        (if changed
            (set-process-coding-system proc decoding encoding))))
     (t
      ;; No async subprocesses...
      (let ((oldbuf (current-buffer))
            (interact-p (eshell-interactive-output-p))
            lbeg lend line proc-buf exit-status)
        (and (not (markerp eshell-last-sync-output-start))
             (setq eshell-last-sync-output-start (point-marker)))
        (setq proc-buf
              (set-buffer (get-buffer-create eshell-scratch-buffer)))
        (erase-buffer)
        (set-buffer oldbuf)
        (run-hook-with-args 'eshell-exec-hook command)
        (setq exit-status
              (apply 'call-process-region
                     (append (list eshell-last-sync-output-start (point)
                                   command t
                                   eshell-scratch-buffer nil)
                             args)))
        ;; When in a pipeline, record the place where the output of
        ;; this process will begin.
        (and eshell-in-pipeline-p
             (set-marker eshell-last-sync-output-start (point)))
        ;; Simulate the effect of the process filter.
        (when (numberp exit-status)
          (set-buffer proc-buf)
          (goto-char (point-min))
          (setq lbeg (point))
          (while (eq 0 (forward-line 1))
            (setq lend (point)
                  line (buffer-substring-no-properties lbeg lend))
            (set-buffer oldbuf)
            (if interact-p
                (eshell-output-filter nil line)
              (eshell-output-object line))
            (setq lbeg lend)
            (set-buffer proc-buf))
          (set-buffer oldbuf))
        (eshell-update-markers eshell-last-output-end)
        ;; Simulate the effect of eshell-sentinel.
        (eshell-close-handles (if (numberp exit-status) exit-status -1))
        (eshell-kill-process-function command exit-status)
        (or eshell-in-pipeline-p
            (setq eshell-last-sync-output-start nil))
        (if (not (numberp exit-status))
          (error "%s: external command failed: %s" command exit-status))
        (setq proc t))))
    proc))

(defun eshell-insertion-filter (proc string)
  "Insert a string into the eshell buffer, or a process/file/buffer.
PROC is the process for which we're inserting output.  STRING is the
output."
  (when (buffer-live-p (process-buffer proc))
    (with-current-buffer (process-buffer proc)
      (let ((entry (assq proc eshell-process-list)))
        (when entry
          (setcar (nthcdr 3 entry)
                  (concat (nth 3 entry) string))
          (unless (nth 4 entry)         ; already being handled?
            (while (nth 3 entry)
              (let ((data (nth 3 entry)))
                (setcar (nthcdr 3 entry) nil)
                (setcar (nthcdr 4 entry) t)
                (eshell-output-object data nil (cadr entry))
                (setcar (nthcdr 4 entry) nil)))))))))

(defun eshell-sentinel (proc string)
  "Generic sentinel for command processes.  Reports only signals.
PROC is the process that's exiting.  STRING is the exit message."
  (when (buffer-live-p (process-buffer proc))
    (with-current-buffer (process-buffer proc)
      (unwind-protect
          (let* ((entry (assq proc eshell-process-list)))
;           (if (not entry)
;               (error "Sentinel called for unowned process `%s'"
;                      (process-name proc))
            (when entry
              (unwind-protect
                  (progn
                    (unless (string= string "run")
                      (unless (string-match "^\\(finished\\|exited\\)" string)
                        (eshell-insertion-filter proc string))
                      (eshell-close-handles (process-exit-status proc) 'nil
                                            (cadr entry))))
                (eshell-remove-process-entry entry))))
        (eshell-kill-process-function proc string)))))

(defun eshell-process-interact (func &optional all query)
  "Interact with a process, using PROMPT if more than one, via FUNC.
If ALL is non-nil, background processes will be interacted with as well.
If QUERY is non-nil, query the user with QUERY before calling FUNC."
  (let (defunct result)
    (dolist (entry eshell-process-list)
      (if (and (memq (process-status (car entry))
                    '(run stop open closed))
               (or all
                   (not (nth 2 entry)))
               (or (not query)
                   (y-or-n-p (format query (process-name (car entry))))))
          (setq result (funcall func (car entry))))
      (unless (memq (process-status (car entry))
                    '(run stop open closed))
        (setq defunct (cons entry defunct))))
    ;; clean up the process list; this can get dirty if an error
    ;; occurred that brought the user into the debugger, and then they
    ;; quit, so that the sentinel was never called.
    (dolist (d defunct)
      (eshell-remove-process-entry d))
    result))

(defcustom eshell-kill-process-wait-time 5
  "Seconds to wait between sending termination signals to a subprocess."
  :type 'integer
  :group 'eshell-proc)

(defcustom eshell-kill-process-signals '(SIGINT SIGQUIT SIGKILL)
  "Signals used to kill processes when an Eshell buffer exits.
Eshell calls each of these signals in order when an Eshell buffer is
killed; if the process is still alive afterwards, Eshell waits a
number of seconds defined by `eshell-kill-process-wait-time', and
tries the next signal in the list."
  :type '(repeat symbol)
  :group 'eshell-proc)

(defcustom eshell-kill-processes-on-exit nil
  "If non-nil, kill active processes when exiting an Eshell buffer.
Emacs will only kill processes owned by that Eshell buffer.

If nil, ownership of background and foreground processes reverts to
Emacs itself, and will die only if the user exits Emacs, calls
`kill-process', or terminates the processes externally.

If `ask', Emacs prompts the user before killing any processes.

If `every', it prompts once for every process.

If t, it kills all buffer-owned processes without asking.

Processes are first sent SIGHUP, then SIGINT, then SIGQUIT, then
SIGKILL.  The variable `eshell-kill-process-wait-time' specifies how
long to delay between signals."
  :type '(choice (const :tag "Kill all, don't ask" t)
                 (const :tag "Ask before killing" ask)
                 (const :tag "Ask for each process" every)
                 (const :tag "Don't kill subprocesses" nil))
  :group 'eshell-proc)

(defun eshell-round-robin-kill (&optional query)
  "Kill current process by trying various signals in sequence.
See the variable `eshell-kill-processes-on-exit'."
  (let ((sigs eshell-kill-process-signals))
    (while sigs
      (eshell-process-interact
       (function
        (lambda (proc)
          (signal-process (process-id proc) (car sigs)))) t query)
      (setq query nil)
      (if (not eshell-process-list)
          (setq sigs nil)
        (sleep-for eshell-kill-process-wait-time)
        (setq sigs (cdr sigs))))))

(defun eshell-query-kill-processes ()
  "Kill processes belonging to the current Eshell buffer, possibly w/ query."
  (when (and eshell-kill-processes-on-exit
             eshell-process-list)
    (save-window-excursion
      (list-processes)
      (if (or (not (eq eshell-kill-processes-on-exit 'ask))
              (y-or-n-p (format "Kill processes owned by `%s'? "
                                (buffer-name))))
          (eshell-round-robin-kill
           (if (eq eshell-kill-processes-on-exit 'every)
               "Kill Eshell child process `%s'? ")))
      (let ((buf (get-buffer "*Process List*")))
        (if (and buf (buffer-live-p buf))
            (kill-buffer buf)))
      (message nil))))

(defun eshell-interrupt-process ()
  "Interrupt a process."
  (interactive)
  (unless (eshell-process-interact 'interrupt-process)
    (eshell-kill-process-function nil "interrupt")))

(defun eshell-kill-process ()
  "Kill a process."
  (interactive)
  (unless (eshell-process-interact 'kill-process)
    (eshell-kill-process-function nil "killed")))

(defun eshell-quit-process ()
  "Send quit signal to process."
  (interactive)
  (unless (eshell-process-interact 'quit-process)
    (eshell-kill-process-function nil "quit")))

;; (defun eshell-stop-process ()
;;  "Send STOP signal to process."
;;  (interactive)
;;  (unless (eshell-process-interact 'stop-process)
;;    (eshell-kill-process-function nil "stopped")))

;; (defun eshell-continue-process ()
;;  "Send CONTINUE signal to process."
;;  (interactive)
;;  (unless (eshell-process-interact 'continue-process)
;;    ;; jww (1999-09-17): this signal is not dealt with yet.  For
;;    ;; example, `eshell-reset' will be called, and so will
;;    ;; `eshell-resume-eval'.
;;    (eshell-kill-process-function nil "continue")))

(defun eshell-send-eof-to-process ()
  "Send EOF to process."
  (interactive)
  (eshell-send-input nil nil t)
  (eshell-process-interact 'process-send-eof))

(provide 'esh-arg)

(require 'esh-mode)

(defgroup eshell-arg nil
  "Argument parsing involves transforming the arguments passed on the
command line into equivalent Lisp forms that, when evaluated, will
yield the values intended."
  :tag "Argument parsing"
  :group 'eshell)

(defcustom eshell-parse-argument-hook
  (list
   ;; a term such as #<buffer NAME>, or #<process NAME> is a buffer
   ;; or process reference
   'eshell-parse-special-reference

   ;; numbers convert to numbers if they stand alone
   (function
    (lambda ()
      (when (and (not eshell-current-argument)
                 (not eshell-current-quoted)
                 (looking-at eshell-number-regexp)
                 (eshell-arg-delimiter (match-end 0)))
        (goto-char (match-end 0))
        (let ((str (match-string 0)))
          (if (> (length str) 0)
              (add-text-properties 0 (length str) '(number t) str))
          str))))

   ;; parse any non-special characters, based on the current context
   (function
    (lambda ()
      (unless eshell-inside-quote-regexp
        (setq eshell-inside-quote-regexp
              (format "[^%s]+"
                      (apply 'string eshell-special-chars-inside-quoting))))
      (unless eshell-outside-quote-regexp
        (setq eshell-outside-quote-regexp
              (format "[^%s]+"
                      (apply 'string eshell-special-chars-outside-quoting))))
      (when (looking-at (if eshell-current-quoted
                            eshell-inside-quote-regexp
                          eshell-outside-quote-regexp))
        (goto-char (match-end 0))
        (let ((str (match-string 0)))
          (if str
              (set-text-properties 0 (length str) nil str))
          str))))

   ;; whitespace or a comment is an argument delimiter
   (function
    (lambda ()
      (let (comment-p)
        (when (or (looking-at "[ \t]+")
                  (and (not eshell-current-argument)
                       (looking-at "#\\([^<'].*\\|$\\)")
                       (setq comment-p t)))
          (if comment-p
              (add-text-properties (match-beginning 0) (match-end 0)
                                   '(comment t)))
          (goto-char (match-end 0))
          (eshell-finish-arg)))))

   ;; backslash before a special character means escape it
   'eshell-parse-backslash

   ;; text beginning with ' is a literally quoted
   'eshell-parse-literal-quote

   ;; text beginning with " is interpolably quoted
   'eshell-parse-double-quote

   ;; argument delimiter
   'eshell-parse-delimiter)
  "Define how to process Eshell command line arguments.
When each function on this hook is called, point will be at the
current position within the argument list.  The function should either
return nil, meaning that it did no argument parsing, or it should
return the result of the parse as a sexp.  It is also responsible for
moving the point forward to reflect the amount of input text that was
parsed.

If no function handles the current character at point, it will be
treated as a literal character."
  :type 'hook
  :group 'eshell-arg)

;;; Code:

;;; User Variables:

(defcustom eshell-arg-load-hook nil
  "A hook that gets run when `eshell-arg' is loaded."
  :version "24.1"                      ; removed eshell-arg-initialize
  :type 'hook
  :group 'eshell-arg)

(defcustom eshell-delimiter-argument-list '(?\; ?& ?\| ?\> ?\s ?\t ?\n)
  "List of characters to recognize as argument separators."
  :type '(repeat character)
  :group 'eshell-arg)

(defcustom eshell-special-chars-inside-quoting '(?\\ ?\")
  "Characters which are still special inside double quotes."
  :type '(repeat character)
  :group 'eshell-arg)

(defcustom eshell-special-chars-outside-quoting
  (append eshell-delimiter-argument-list '(?# ?! ?\\ ?\" ?\'))
  "Characters that require escaping outside of double quotes.
Without escaping them, they will introduce a change in the argument."
  :type '(repeat character)
  :group 'eshell-arg)

;;; Internal Variables:

(defvar eshell-current-argument nil)
(defvar eshell-current-modifiers nil)
(defvar eshell-arg-listified nil)
(defvar eshell-nested-argument nil)
(defvar eshell-current-quoted nil)
(defvar eshell-inside-quote-regexp nil)
(defvar eshell-outside-quote-regexp nil)

;;; Functions:

(defun eshell-arg-initialize ()
  "Initialize the argument parsing code."
  (define-key eshell-command-map [(meta ?b)] 'eshell-insert-buffer-name)
  (set (make-local-variable 'eshell-inside-quote-regexp) nil)
  (set (make-local-variable 'eshell-outside-quote-regexp) nil))

(defun eshell-insert-buffer-name (buffer-name)
  "Insert BUFFER-NAME into the current buffer at point."
  (interactive "BName of buffer: ")
  (insert-and-inherit "#<buffer " buffer-name ">"))

(defsubst eshell-escape-arg (string)
  "Return STRING with the `escaped' property on it."
  (if (stringp string)
      (add-text-properties 0 (length string) '(escaped t) string))
  string)

(defun eshell-resolve-current-argument ()
  "If there are pending modifications to be made, make them now."
  (when eshell-current-argument
    (when eshell-arg-listified
      (let ((parts eshell-current-argument))
        (while parts
          (unless (stringp (car parts))
            (setcar parts
                    (list 'eshell-to-flat-string (car parts))))
          (setq parts (cdr parts)))
        (setq eshell-current-argument
              (list 'eshell-convert
                    (append (list 'concat) eshell-current-argument))))
      (setq eshell-arg-listified nil))
    (while eshell-current-modifiers
      (setq eshell-current-argument
            (list (car eshell-current-modifiers) eshell-current-argument)
            eshell-current-modifiers (cdr eshell-current-modifiers))))
  (setq eshell-current-modifiers nil))

(defun eshell-finish-arg (&optional argument)
  "Finish the current argument being processed."
  (if argument
      (setq eshell-current-argument argument))
  (throw 'eshell-arg-done t))

(defsubst eshell-arg-delimiter (&optional pos)
  "Return non-nil if POS is an argument delimiter.
If POS is nil, the location of point is checked."
  (let ((pos (or pos (point))))
    (or (= pos (point-max))
        (memq (char-after pos) eshell-delimiter-argument-list))))

(defun eshell-quote-argument (string)
  "Return STRING with magic characters quoted.
Magic characters are those in `eshell-special-chars-outside-quoting'."
  (let ((index 0))
    (mapconcat (lambda (c)
                 (prog1
                     (or (eshell-quote-backslash string index)
                         (char-to-string c))
                   (setq index (1+ index))))
               string
               "")))

;; Argument parsing

(defun eshell-parse-arguments (beg end)
  "Parse all of the arguments at point from BEG to END.
Returns the list of arguments in their raw form.
Point is left at the end of the arguments."
  (save-excursion
    (save-restriction
      (goto-char beg)
      (narrow-to-region beg end)
      (let ((inhibit-point-motion-hooks t)
            (args (list t))
            delim)
        (with-silent-modifications
          (remove-text-properties (point-min) (point-max)
                                  '(arg-begin nil arg-end nil))
          (if (setq
               delim
               (catch 'eshell-incomplete
                 (while (not (eobp))
                   (let* ((here (point))
                          (arg (eshell-parse-argument)))
                     (if (= (point) here)
                         (error "Failed to parse argument '%s'"
                                (buffer-substring here (point-max))))
                     (and arg (nconc args (list arg)))))))
              (throw 'eshell-incomplete (if (listp delim)
                                            delim
                                          (list delim (point) (cdr args)))))
          (cdr args))))))

(defun eshell-parse-argument ()
  "Get the next argument.  Leave point after it."
  (let* ((outer (null eshell-nested-argument))
         (arg-begin (and outer (point)))
         (eshell-nested-argument t)
         eshell-current-argument
         eshell-current-modifiers
         eshell-arg-listified)
    (catch 'eshell-arg-done
      (while (not (eobp))
        (let ((result
               (or (run-hook-with-args-until-success
                    'eshell-parse-argument-hook)
                   (prog1
                       (char-to-string (char-after))
                     (forward-char)))))
          (if (not eshell-current-argument)
              (setq eshell-current-argument result)
            (unless eshell-arg-listified
              (setq eshell-current-argument
                    (list eshell-current-argument)
                    eshell-arg-listified t))
            (nconc eshell-current-argument (list result))))))
    (when (and outer eshell-current-argument)
      (add-text-properties arg-begin (1+ arg-begin)
                           '(arg-begin t rear-nonsticky
                                       (arg-begin arg-end)))
      (add-text-properties (1- (point)) (point)
                           '(arg-end t rear-nonsticky
                                     (arg-end arg-begin))))
    (eshell-resolve-current-argument)
    eshell-current-argument))

(defsubst eshell-operator (&rest _args)
  "A stub function that generates an error if a floating operator is found."
  (error "Unhandled operator in input text"))

(defsubst eshell-looking-at-backslash-return (pos)
  "Test whether a backslash-return sequence occurs at POS."
  (and (eq (char-after pos) ?\\)
       (or (= (1+ pos) (point-max))
           (and (eq (char-after (1+ pos)) ?\n)
                (= (+ pos 2) (point-max))))))

(defun eshell-quote-backslash (string &optional index)
  "Intelligently backslash the character occurring in STRING at INDEX.
If the character is itself a backslash, it needs no escaping."
  (let ((char (aref string index)))
    (if (and (eq char ?\\)
             ;; In Emacs directory-sep-char is always ?/, so this does nothing.
             (not (and (featurep 'xemacs)
                       (featurep 'mswindows)
                       (eq directory-sep-char ?\\)
                       (eq (1- (string-width string))
                           index))))
        (char-to-string char)
      (if (memq char eshell-special-chars-outside-quoting)
          (string ?\\ char)))))

(defun eshell-parse-backslash ()
  "Parse a single backslash (\) character, which might mean escape.
It only means escape if the character immediately following is a
special character that is not itself a backslash."
  (when (eq (char-after) ?\\)
    (if (eshell-looking-at-backslash-return (point))
        (throw 'eshell-incomplete ?\\)
      (if (and (not (eq (char-after (1+ (point))) ?\\))
               (if eshell-current-quoted
                   (memq (char-after (1+ (point)))
                         eshell-special-chars-inside-quoting)
                 (memq (char-after (1+ (point)))
                       eshell-special-chars-outside-quoting)))
          (progn
            (forward-char 2)
            (list 'eshell-escape-arg
                  (char-to-string (char-before))))
        ;; allow \\<RET> to mean a literal "\" character followed by a
        ;; normal return, rather than a backslash followed by a line
        ;; continuation (i.e., "\\ + \n" rather than "\ + \\n").  This
        ;; is necessary because backslashes in Eshell are not special
        ;; unless they either precede something special, or precede a
        ;; backslash that precedes something special.  (Mainly this is
        ;; done to make using backslash on Windows systems more
        ;; natural-feeling).
        (if (eshell-looking-at-backslash-return (1+ (point)))
            (forward-char))
        (forward-char)
        "\\"))))

(defun eshell-parse-literal-quote ()
  "Parse a literally quoted string.  Nothing has special meaning!"
  (if (eq (char-after) ?\')
      (let ((end (eshell-find-delimiter ?\' ?\')))
        (if (not end)
            (throw 'eshell-incomplete ?\')
          (let ((string (buffer-substring-no-properties (1+ (point)) end)))
            (goto-char (1+ end))
            (while (string-match "''" string)
              (setq string (replace-match "'" t t string)))
            (list 'eshell-escape-arg string))))))

(defun eshell-parse-double-quote ()
  "Parse a double quoted string, which allows for variable interpolation."
  (when (eq (char-after) ?\")
    (let* ((end (eshell-find-delimiter ?\" ?\" nil nil t))
           (eshell-current-quoted t))
      (if (not end)
          (throw 'eshell-incomplete ?\")
        (prog1
            (save-restriction
              (forward-char)
              (narrow-to-region (point) end)
              (let ((arg (eshell-parse-argument)))
                (if (eq arg nil)
                    ""
                  (list 'eshell-escape-arg arg))))
          (goto-char (1+ end)))))))

(defun eshell-parse-special-reference ()
  "Parse a special syntax reference, of the form '#<type arg>'."
  (if (and (not eshell-current-argument)
           (not eshell-current-quoted)
           (looking-at "#<\\(buffer\\|process\\)\\s-"))
      (let ((here (point)))
        (goto-char (match-end 0))
        (let* ((buffer-p (string= (match-string 1) "buffer"))
               (end (eshell-find-delimiter ?\< ?\>)))
          (if (not end)
              (throw 'eshell-incomplete ?\<)
            (if (eshell-arg-delimiter (1+ end))
                (prog1
                    (list (if buffer-p 'get-buffer-create 'get-process)
                          (buffer-substring-no-properties (point) end))
                  (goto-char (1+ end)))
              (ignore (goto-char here))))))))

(defun eshell-parse-delimiter ()
  "Parse an argument delimiter, which is essentially a command operator."
  ;; this `eshell-operator' keyword gets parsed out by
  ;; `eshell-separate-commands'.  Right now the only possibility for
  ;; error is an incorrect output redirection specifier.
  (when (looking-at "[&|;\n]\\s-*")
    (let ((end (match-end 0)))
    (if eshell-current-argument
        (eshell-finish-arg)
      (eshell-finish-arg
       (prog1
           (list 'eshell-operator
                 (cond
                  ((eq (char-after end) ?\&)
                   (setq end (1+ end)) "&&")
                  ((eq (char-after end) ?\|)
                   (setq end (1+ end)) "||")
                  ((eq (char-after) ?\n) ";")
                  (t
                   (char-to-string (char-after)))))
         (goto-char end)))))))

(provide 'esh-io)

(require 'esh-arg)
(require 'esh-util)

(eval-when-compile
  (require 'cl-lib))

(defgroup eshell-io nil
  "Eshell's I/O management code provides a scheme for treating many
different kinds of objects -- symbols, files, buffers, etc. -- as
though they were files."
  :tag "I/O management"
  :group 'eshell)

;;; User Variables:

(defcustom eshell-io-load-hook nil
  "A hook that gets run when `eshell-io' is loaded."
  :version "24.1"                       ; removed eshell-io-initialize
  :type 'hook
  :group 'eshell-io)

(defcustom eshell-number-of-handles 3
  "The number of file handles that eshell supports.
Currently this is standard input, output and error.  But even all of
these Emacs does not currently support with asynchronous processes
\(which is what eshell uses so that you can continue doing work in
other buffers) ."
  :type 'integer
  :group 'eshell-io)

(defcustom eshell-output-handle 1
  "The index of the standard output handle."
  :type 'integer
  :group 'eshell-io)

(defcustom eshell-error-handle 2
  "The index of the standard error handle."
  :type 'integer
  :group 'eshell-io)

(defcustom eshell-buffer-shorthand nil
  "If non-nil, a symbol name can be used for a buffer in redirection.
If nil, redirecting to a buffer requires buffer name syntax.  If this
variable is set, redirection directly to Lisp symbols will be
impossible.

Example:

  echo hello > '*scratch*  ; works if `eshell-buffer-shorthand' is t
  echo hello > #<buffer *scratch*>  ; always works"
  :type 'boolean
  :group 'eshell-io)

(defcustom eshell-print-queue-size 5
  "The size of the print queue, for doing buffered printing.
This is basically a speed enhancement, to avoid blocking the Lisp code
from executing while Emacs is redisplaying."
  :type 'integer
  :group 'eshell-io)

(defvar x-select-enable-clipboard)      ; term/common-win

(defcustom eshell-virtual-targets
  '(("/dev/eshell" eshell-interactive-print nil)
    ("/dev/kill" (lambda (mode)
                   (if (eq mode 'overwrite)
                       (kill-new ""))
                   'eshell-kill-append) t)
    ("/dev/clip" (lambda (mode)
                   (if (eq mode 'overwrite)
                       (let ((x-select-enable-clipboard t))
                         (kill-new "")))
                   'eshell-clipboard-append) t))
  "Map virtual devices name to Emacs Lisp functions.
If the user specifies any of the filenames above as a redirection
target, the function in the second element will be called.

If the third element is non-nil, the redirection mode is passed as an
argument (which is the symbol `overwrite', `append' or `insert'), and
the function is expected to return another function -- which is the
output function.  Otherwise, the second element itself is the output
function.

The output function is then called repeatedly with single strings,
which represents successive pieces of the output of the command, until nil
is passed, meaning EOF.

NOTE: /dev/null is handled specially as a virtual target, and should
not be added to this variable."
  :type '(repeat
          (list (string :tag "Target")
                function
                (choice (const :tag "Func returns output-func" t)
                        (const :tag "Func is output-func" nil))))
  :group 'eshell-io)

(put 'eshell-virtual-targets 'risky-local-variable t)

;;; Internal Variables:

(defvar eshell-current-handles nil)

(defvar eshell-last-command-status 0
  "The exit code from the last command.  0 if successful.")

(defvar eshell-last-command-result nil
  "The result of the last command.  Not related to success.")

(defvar eshell-output-file-buffer nil
  "If non-nil, the current buffer is a file output buffer.")

(defvar eshell-print-count)
(defvar eshell-current-redirections)

;;; Functions:

(defun eshell-io-initialize ()
  "Initialize the I/O subsystem code."
  (add-hook 'eshell-parse-argument-hook
            'eshell-parse-redirection nil t)
  (make-local-variable 'eshell-current-redirections)
  (add-hook 'eshell-pre-rewrite-command-hook
            'eshell-strip-redirections nil t)
  (add-function :filter-return (local 'eshell-post-rewrite-command-function)
                #'eshell--apply-redirections))

(defun eshell-parse-redirection ()
  "Parse an output redirection, such as '2>'."
  (if (and (not eshell-current-quoted)
           (looking-at "\\([0-9]\\)?\\(<\\|>+\\)&?\\([0-9]\\)?\\s-*"))
      (if eshell-current-argument
          (eshell-finish-arg)
        (let ((sh (match-string 1))
              (oper (match-string 2))
;             (th (match-string 3))
              )
          (if (string= oper "<")
              (error "Eshell does not support input redirection"))
          (eshell-finish-arg
           (prog1
               (list 'eshell-set-output-handle
                     (or (and sh (string-to-number sh)) 1)
                     (list 'quote
                           (aref [overwrite append insert]
                                 (1- (length oper)))))
             (goto-char (match-end 0))))))))

(defun eshell-strip-redirections (terms)
  "Rewrite any output redirections in TERMS."
  (setq eshell-current-redirections (list t))
  (let ((tl terms)
        (tt (cdr terms)))
    (while tt
      (if (not (and (consp (car tt))
                    (eq (caar tt) 'eshell-set-output-handle)))
          (setq tt (cdr tt)
                tl (cdr tl))
        (unless (cdr tt)
          (error "Missing redirection target"))
        (nconc eshell-current-redirections
               (list (list 'ignore
                           (append (car tt) (list (cadr tt))))))
        (setcdr tl (cddr tt))
        (setq tt (cddr tt))))
    (setq eshell-current-redirections
          (cdr eshell-current-redirections))))

(defun eshell--apply-redirections (cmd)
  "Apply any redirection which were specified for COMMAND."
  (if eshell-current-redirections
      `(progn
         ,@eshell-current-redirections
         ,cmd)
    cmd))

(defun eshell-create-handles
  (stdout output-mode &optional stderr error-mode)
  "Create a new set of file handles for a command.
The default location for standard output and standard error will go to
STDOUT and STDERR, respectively.
OUTPUT-MODE and ERROR-MODE are either `overwrite', `append' or `insert';
a nil value of mode defaults to `insert'."
  (let ((handles (make-vector eshell-number-of-handles nil))
        (output-target (eshell-get-target stdout output-mode))
        (error-target (eshell-get-target stderr error-mode)))
    (aset handles eshell-output-handle (cons output-target 1))
    (aset handles eshell-error-handle
          (cons (if stderr error-target output-target) 1))
    handles))

(defun eshell-protect-handles (handles)
  "Protect the handles in HANDLES from a being closed."
  (let ((idx 0))
    (while (< idx eshell-number-of-handles)
      (if (aref handles idx)
          (setcdr (aref handles idx)
                  (1+ (cdr (aref handles idx)))))
      (setq idx (1+ idx))))
  handles)

(defun eshell-close-target (target status)
  "Close an output TARGET, passing STATUS as the result.
STATUS should be non-nil on successful termination of the output."
  (cond
   ((symbolp target) nil)

   ;; If we were redirecting to a file, save the file and close the
   ;; buffer.
   ((markerp target)
    (let ((buf (marker-buffer target)))
      (when buf                         ; somebody's already killed it!
        (save-current-buffer
          (set-buffer buf)
          (when eshell-output-file-buffer
            (save-buffer)
            (when (eq eshell-output-file-buffer t)
              (or status (set-buffer-modified-p nil))
              (kill-buffer buf)))))))

   ;; If we're redirecting to a process (via a pipe, or process
   ;; redirection), send it EOF so that it knows we're finished.
   ((eshell-processp target)
    (if (eq (process-status target) 'run)
        (process-send-eof target)))

   ;; A plain function redirection needs no additional arguments
   ;; passed.
   ((functionp target)
    (funcall target status))

   ;; But a more complicated function redirection (which can only
   ;; happen with aliases at the moment) has arguments that need to be
   ;; passed along with it.
   ((consp target)
    (apply (car target) status (cdr target)))))

(defun eshell-close-handles (exit-code &optional result handles)
  "Close all of the current handles, taking refcounts into account.
EXIT-CODE is the process exit code; mainly, it is zero, if the command
completed successfully.  RESULT is the quoted value of the last
command.  If nil, then the meta variables for keeping track of the
last execution result should not be changed."
  (let ((idx 0))
    (cl-assert (or (not result) (eq (car result) 'quote)))
    (setq eshell-last-command-status exit-code
          eshell-last-command-result (cadr result))
    (while (< idx eshell-number-of-handles)
      (let ((handles (or handles eshell-current-handles)))
        (when (aref handles idx)
          (setcdr (aref handles idx)
                  (1- (cdr (aref handles idx))))
          (when (= (cdr (aref handles idx)) 0)
            (let ((target (car (aref handles idx))))
              (if (not (listp target))
                  (eshell-close-target target (= exit-code 0))
                (while target
                  (eshell-close-target (car target) (= exit-code 0))
                  (setq target (cdr target)))))
            (setcar (aref handles idx) nil))))
      (setq idx (1+ idx)))
    nil))

(defun eshell-kill-append (string)
  "Call `kill-append' with STRING, if it is indeed a string."
  (if (stringp string)
      (kill-append string nil)))

(defun eshell-clipboard-append (string)
  "Call `kill-append' with STRING, if it is indeed a string."
  (if (stringp string)
      (let ((x-select-enable-clipboard t))
        (kill-append string nil))))

(defun eshell-get-target (target &optional mode)
  "Convert TARGET, which is a raw argument, into a valid output target.
MODE is either `overwrite', `append' or `insert'; if it is omitted or nil,
it defaults to `insert'."
  (setq mode (or mode 'insert))
  (cond
   ((stringp target)
    (let ((redir (assoc target eshell-virtual-targets)))
      (if redir
          (if (nth 2 redir)
              (funcall (nth 1 redir) mode)
            (nth 1 redir))
        (let* ((exists (get-file-buffer target))
               (buf (find-file-noselect target t)))
          (with-current-buffer buf
            (if buffer-file-read-only
                (error "Cannot write to read-only file `%s'" target))
            (setq buffer-read-only nil)
            (set (make-local-variable 'eshell-output-file-buffer)
                 (if (eq exists buf) 0 t))
            (cond ((eq mode 'overwrite)
                   (erase-buffer))
                  ((eq mode 'append)
                   (goto-char (point-max))))
            (point-marker))))))

   ((or (bufferp target)
        (and (boundp 'eshell-buffer-shorthand)
             (symbol-value 'eshell-buffer-shorthand)
             (symbolp target)
             (not (memq target '(t nil)))))
    (let ((buf (if (bufferp target)
                   target
                 (get-buffer-create
                  (symbol-name target)))))
      (with-current-buffer buf
        (cond ((eq mode 'overwrite)
               (erase-buffer))
              ((eq mode 'append)
               (goto-char (point-max))))
        (point-marker))))

   ((functionp target) nil)

   ((symbolp target)
    (if (eq mode 'overwrite)
        (set target nil))
    target)

   ((or (eshell-processp target)
        (markerp target))
    target)

   (t
    (error "Invalid redirection target: %s"
           (eshell-stringify target)))))

(defvar grep-null-device)

(defun eshell-set-output-handle (index mode &optional target)
  "Set handle INDEX, using MODE, to point to TARGET."
  (when target
    (if (and (stringp target)
             (or (cond
                  ((boundp 'null-device)
                   (string= target null-device))
                  ((boundp 'grep-null-device)
                   (string= target grep-null-device))
                  (t nil))
                 (string= target "/dev/null")))
        (aset eshell-current-handles index nil)
      (let ((where (eshell-get-target target mode))
            (current (car (aref eshell-current-handles index))))
        (if (and (listp current)
                 (not (member where current)))
            (setq current (append current (list where)))
          (setq current (list where)))
        (if (not (aref eshell-current-handles index))
            (aset eshell-current-handles index (cons nil 1)))
        (setcar (aref eshell-current-handles index) current)))))

(defun eshell-interactive-output-p ()
  "Return non-nil if current handles are bound for interactive display."
  (and (eq (car (aref eshell-current-handles
                      eshell-output-handle)) t)
       (eq (car (aref eshell-current-handles
                      eshell-error-handle)) t)))

(defvar eshell-print-queue nil)
(defvar eshell-print-queue-count -1)

(defsubst eshell-print (object)
  "Output OBJECT to the standard output handle."
  (eshell-output-object object eshell-output-handle))

(defun eshell-flush (&optional reset-p)
  "Flush out any lines that have been queued for printing.
Must be called before printing begins with -1 as its argument, and
after all printing is over with no argument."
  (ignore
   (if reset-p
       (setq eshell-print-queue nil
             eshell-print-queue-count reset-p)
     (if eshell-print-queue
         (eshell-print eshell-print-queue))
     (eshell-flush 0))))

(defun eshell-init-print-buffer ()
  "Initialize the buffered printing queue."
  (eshell-flush -1))

(defun eshell-buffered-print (&rest strings)
  "A buffered print -- *for strings only*."
  (if (< eshell-print-queue-count 0)
      (progn
        (eshell-print (apply 'concat strings))
        (setq eshell-print-queue-count 0))
    (if (= eshell-print-queue-count eshell-print-queue-size)
        (eshell-flush))
    (setq eshell-print-queue
          (concat eshell-print-queue (apply 'concat strings))
          eshell-print-queue-count (1+ eshell-print-queue-count))))

(defsubst eshell-error (object)
  "Output OBJECT to the standard error handle."
  (eshell-output-object object eshell-error-handle))

(defsubst eshell-errorn (object)
  "Output OBJECT followed by a newline to the standard error handle."
  (eshell-error object)
  (eshell-error "\n"))

(defsubst eshell-printn (object)
  "Output OBJECT followed by a newline to the standard output handle."
  (eshell-print object)
  (eshell-print "\n"))

(autoload 'eshell-output-filter "esh-mode")

(defun eshell-output-object-to-target (object target)
  "Insert OBJECT into TARGET.
Returns what was actually sent, or nil if nothing was sent."
  (cond
   ((functionp target)
    (funcall target object))

   ((symbolp target)
    (if (eq target t)                   ; means "print to display"
        (eshell-output-filter nil (eshell-stringify object))
      (if (not (symbol-value target))
          (set target object)
        (setq object (eshell-stringify object))
        (if (not (stringp (symbol-value target)))
            (set target (eshell-stringify
                         (symbol-value target))))
        (set target (concat (symbol-value target) object)))))

   ((markerp target)
    (if (buffer-live-p (marker-buffer target))
        (with-current-buffer (marker-buffer target)
          (let ((moving (= (point) target)))
            (save-excursion
              (goto-char target)
              (unless (stringp object)
                (setq object (eshell-stringify object)))
              (insert-and-inherit object)
              (set-marker target (point-marker)))
            (if moving
                (goto-char target))))))

   ((eshell-processp target)
    (when (eq (process-status target) 'run)
      (unless (stringp object)
        (setq object (eshell-stringify object)))
      (process-send-string target object)))

   ((consp target)
    (apply (car target) object (cdr target))))
  object)

(defun eshell-output-object (object &optional handle-index handles)
  "Insert OBJECT, using HANDLE-INDEX specifically)."
  (let ((target (car (aref (or handles eshell-current-handles)
                           (or handle-index eshell-output-handle)))))
    (if (and target (not (listp target)))
        (eshell-output-object-to-target object target)
      (while target
        (eshell-output-object-to-target object (car target))
        (setq target (cdr target))))))

(provide 'esh-ext)

(require 'esh-util)

(eval-when-compile
  (require 'cl-lib)
  (require 'esh-io)
  (require 'esh-cmd))
(require 'esh-opt)

(defgroup eshell-ext nil
  "External commands are invoked when operating system executables are
loaded into memory, thus beginning a new process."
  :tag "External commands"
  :group 'eshell)

;;; User Variables:

(defcustom eshell-ext-load-hook nil
  "A hook that gets run when `eshell-ext' is loaded."
  :version "24.1"                       ; removed eshell-ext-initialize
  :type 'hook
  :group 'eshell-ext)

(defcustom eshell-binary-suffixes exec-suffixes
  "A list of suffixes used when searching for executable files."
  :type '(repeat string)
  :group 'eshell-ext)

(defcustom eshell-force-execution nil
  "If non-nil, try to execute binary files regardless of permissions.
This can be useful on systems like Windows, where the operating system
doesn't happen to honor the permission bits in certain cases; or in
cases where you want to associate an interpreter with a particular
kind of script file, but the language won't let you but a '#!'
interpreter line in the file, and you don't want to make it executable
since nothing else but Eshell will be able to understand
`eshell-interpreter-alist'."
  :type 'boolean
  :group 'eshell-ext)

(defun eshell-search-path (name)
  "Search the environment path for NAME."
  (if (file-name-absolute-p name)
      name
    (let ((list (eshell-parse-colon-path eshell-path-env))
          suffixes n1 n2 file)
      (while list
        (setq n1 (concat (car list) name))
        (setq suffixes eshell-binary-suffixes)
        (while suffixes
          (setq n2 (concat n1 (car suffixes)))
          (if (and (or (file-executable-p n2)
                       (and eshell-force-execution
                            (file-readable-p n2)))
                   (not (file-directory-p n2)))
              (setq file n2 suffixes nil list nil))
          (setq suffixes (cdr suffixes)))
        (setq list (cdr list)))
      file)))

;; This file provides itself then eval-when-compile loads files that require it.
;; This causes spurious "might not be defined at runtime" warnings.
(declare-function eshell-search-path "esh-ext" (name))

(defcustom eshell-windows-shell-file
  (if (eshell-under-windows-p)
      (if (string-match "\\(cmdproxy\\|sh\\)\\.\\(com\\|exe\\)"
                        shell-file-name)
          (or (eshell-search-path "cmd.exe")
              (eshell-search-path "command.com"))
        shell-file-name))
  "The name of the shell command to use for DOS/Windows batch files.
This defaults to nil on non-Windows systems, where this variable is
wholly ignored."
  :type '(choice file (const nil))
  :group 'eshell-ext)

(autoload 'eshell-parse-command "esh-cmd")

(defsubst eshell-invoke-batch-file (&rest args)
  "Invoke a .BAT or .CMD file on DOS/Windows systems."
  ;; since CMD.EXE can't handle forward slashes in the initial
  ;; argument...
  (setcar args (subst-char-in-string ?/ ?\\ (car args)))
  (throw 'eshell-replace-command
         (eshell-parse-command
          (eshell-quote-argument eshell-windows-shell-file)
          (cons "/c" args))))

(defcustom eshell-interpreter-alist
  (if (eshell-under-windows-p)
      '(("\\.\\(bat\\|cmd\\)\\'" . eshell-invoke-batch-file)))
  "An alist defining interpreter substitutions.
Each member is a cons cell of the form:

  (MATCH . INTERPRETER)

MATCH should be a regexp, which is matched against the command
name, or a function of arity 2 receiving the COMMAND and its
ARGS (a list).  If either returns a non-nil value, then
INTERPRETER will be used for that command.

If INTERPRETER is a string, it will be called as the command name,
with the original command name passed as the first argument, with all
subsequent arguments following.  If INTERPRETER is a function, it will
be called with all of those arguments.  Note that interpreter
functions should throw `eshell-replace-command' with the alternate
command form, or they should return a value compatible with the
possible return values of `eshell-external-command', which see."
  :type '(repeat (cons (choice regexp (function :tag "Predicate"))
                       (choice string (function :tag "Interpreter"))))
  :group 'eshell-ext)

(defcustom eshell-alternate-command-hook nil
  "A hook run whenever external command lookup fails.
If a functions wishes to provide an alternate command, they must throw
it using the tag `eshell-replace-command'.  This is done because the
substituted command need not be external at all, and therefore must be
passed up to a higher level for re-evaluation.

Or, if the function returns a filename, that filename will be invoked
with the current command arguments rather than the command specified
by the user on the command line."
  :type 'hook
  :group 'eshell-ext)

(defcustom eshell-command-interpreter-max-length 256
  "The maximum length of any command interpreter string, plus args."
  :type 'integer
  :group 'eshell-ext)

(defcustom eshell-explicit-command-char ?*
  "If this char occurs before a command name, call it externally.
That is, although `vi' may be an alias, `\vi' will always call the
external version."
  :type 'character
  :group 'eshell-ext)

;;; Functions:

(defun eshell-ext-initialize ()
  "Initialize the external command handling code."
  (add-hook 'eshell-named-command-hook 'eshell-explicit-command nil t))

(defun eshell-explicit-command (command args)
  "If a command name begins with `*', call it externally always.
This bypasses all Lisp functions and aliases."
  (when (and (> (length command) 1)
             (eq (aref command 0) eshell-explicit-command-char))
    (let ((cmd (eshell-search-path (substring command 1))))
      (if cmd
          (or (eshell-external-command cmd args)
              (error "%s: external command failed" cmd))
        (error "%s: external command not found"
               (substring command 1))))))

(autoload 'eshell-close-handles "esh-io")

(defun eshell-remote-command (command args)
  "Insert output from a remote COMMAND, using ARGS.
A remote command is something that executes on a different machine.
An external command simply means external to Emacs.

Note that this function is very crude at the moment.  It gathers up
all the output from the remote command, and sends it all at once,
causing the user to wonder if anything's really going on..."
  (let ((outbuf (generate-new-buffer " *eshell remote output*"))
        (errbuf (generate-new-buffer " *eshell remote error*"))
        (command (or (file-remote-p command 'localname) command))
        (exitcode 1))
    (unwind-protect
        (progn
          (setq exitcode
                (shell-command
                 (mapconcat 'shell-quote-argument
                            (append (list command) args) " ")
                 outbuf errbuf))
          (eshell-print (with-current-buffer outbuf (buffer-string)))
          (eshell-error (with-current-buffer errbuf (buffer-string))))
      (eshell-close-handles exitcode 'nil)
      (kill-buffer outbuf)
      (kill-buffer errbuf))))

(defun eshell-external-command (command args)
  "Insert output from an external COMMAND, using ARGS."
  (setq args (eshell-stringify-list (eshell-flatten-list args)))
  (let ((interp (eshell-find-interpreter
                 command
                 args
                 ;; `eshell-find-interpreter' does not work correctly
                 ;; for Tramp file name syntax.  But we don't need to
                 ;; know the interpreter in that case, therefore the
                 ;; check is suppressed.
                 (or (and (stringp command) (file-remote-p command))
                     (file-remote-p default-directory)))))
    (cl-assert interp)
    (if (functionp (car interp))
        (apply (car interp) (append (cdr interp) args))
      (eshell-gather-process-output
       (car interp) (append (cdr interp) args)))))

(defun eshell/addpath (&rest args)
  "Add a set of paths to PATH."
  (eshell-eval-using-options
   "addpath" args
   '((?b "begin" nil prepend "add path element at beginning")
     (?h "help" nil nil  "display this usage message")
     :usage "[-b] PATH
Adds the given PATH to $PATH.")
   (if args
       (progn
         (setq eshell-path-env (getenv "PATH")
               args (mapconcat 'identity args path-separator)
               eshell-path-env
               (if prepend
                   (concat args path-separator eshell-path-env)
                 (concat eshell-path-env path-separator args)))
         (setenv "PATH" eshell-path-env))
     (dolist (dir (parse-colon-path (getenv "PATH")))
       (eshell-printn dir)))))

(put 'eshell/addpath 'eshell-no-numeric-conversions t)

(defun eshell-script-interpreter (file)
  "Extract the script to run from FILE, if it has #!<interp> in it.
Return nil, or a list of the form:

  (INTERPRETER [ARGS] FILE)"
  (let ((maxlen eshell-command-interpreter-max-length))
    (if (and (file-readable-p file)
             (file-regular-p file))
        (with-temp-buffer
          (insert-file-contents-literally file nil 0 maxlen)
          (if (looking-at "#![ \t]*\\([^ \r\t\n]+\\)\\([ \t]+\\(.+\\)\\)?")
              (if (match-string 3)
                  (list (match-string 1)
                        (match-string 3)
                        file)
                (list (match-string 1)
                      file)))))))

(defun eshell-find-interpreter (file args &optional no-examine-p)
  "Find the command interpreter with which to execute FILE.
If NO-EXAMINE-P is non-nil, FILE will not be inspected for a script
line of the form #!<interp>."
  (let ((finterp
         (catch 'found
           (ignore
            (dolist (possible eshell-interpreter-alist)
              (cond
               ((functionp (car possible))
                (let ((fn (car possible)))
                  (and (funcall fn file args)
                       (throw 'found (cdr possible)))))
               ((stringp (car possible))
                (and (string-match (car possible) file)
                     (throw 'found (cdr possible))))
               (t
                (error "Invalid interpreter-alist test"))))))))
    (if finterp                         ; first check
        (list finterp file)
      (let ((fullname (if (file-name-directory file) file
                        (eshell-search-path file)))
            (suffixes eshell-binary-suffixes))
        (if (and fullname (not (or eshell-force-execution
                                   (file-executable-p fullname))))
            (while suffixes
              (let ((try (concat fullname (car suffixes))))
                (if (or (file-executable-p try)
                        (and eshell-force-execution
                             (file-readable-p try)))
                    (setq fullname try suffixes nil)
                  (setq suffixes (cdr suffixes))))))
        (cond ((not (and fullname (file-exists-p fullname)))
               (let ((name (or fullname file)))
                 (unless (setq fullname
                               (run-hook-with-args-until-success
                                'eshell-alternate-command-hook file))
                   (error "%s: command not found" name))))
              ((not (or eshell-force-execution
                        (file-executable-p fullname)))
               (error "%s: Permission denied" fullname)))
        (let (interp)
          (unless no-examine-p
            (setq interp (eshell-script-interpreter fullname))
            (if interp
                (setq interp
                      (cons (car (eshell-find-interpreter (car interp) args t))
                            (cdr interp)))))
          (or interp (list fullname)))))))

(require 'esh-util)
(unless (featurep 'xemacs)
  (require 'eldoc))
(require 'esh-arg)
(require 'esh-proc)
(require 'esh-ext)

(eval-when-compile
  (require 'cl-lib)
  (require 'pcomplete))


(defgroup eshell-cmd nil
  "Executing an Eshell command is as simple as typing it in and
pressing <RET>.  There are several different kinds of commands,
however."
  :tag "Command invocation"
  ;; :link '(info-link "(eshell)Command invocation")
  :group 'eshell)

(defcustom eshell-prefer-lisp-functions nil
  "If non-nil, prefer Lisp functions to external commands."
  :type 'boolean
  :group 'eshell-cmd)

(defcustom eshell-lisp-regexp "\\([(`]\\|#'\\)"
  "A regexp which, if matched at beginning of an argument, means Lisp.
Such arguments will be passed to `read', and then evaluated."
  :type 'regexp
  :group 'eshell-cmd)

(defcustom eshell-pre-command-hook nil
  "A hook run before each interactive command is invoked."
  :type 'hook
  :group 'eshell-cmd)

(defcustom eshell-post-command-hook nil
  "A hook run after each interactive command is invoked."
  :type 'hook
  :group 'eshell-cmd)

(defcustom eshell-prepare-command-hook nil
  "A set of functions called to prepare a named command.
The command name and its argument are in `eshell-last-command-name'
and `eshell-last-arguments'.  The functions on this hook can change
the value of these symbols if necessary.

To prevent a command from executing at all, set
`eshell-last-command-name' to nil."
  :type 'hook
  :group 'eshell-cmd)

(defcustom eshell-named-command-hook nil
  "A set of functions called before a named command is invoked.
Each function will be passed the command name and arguments that were
passed to `eshell-named-command'.

If any of the functions returns a non-nil value, the named command
will not be invoked, and that value will be returned from
`eshell-named-command'.

In order to substitute an alternate command form for execution, the
hook function should throw it using the tag `eshell-replace-command'.
For example:

  (add-hook 'eshell-named-command-hook 'subst-with-cd)
  (defun subst-with-cd (command args)
    (throw 'eshell-replace-command
           (eshell-parse-command \"cd\" args)))

Although useless, the above code will cause any non-glob, non-Lisp
command (i.e., 'ls' as opposed to '*ls' or '(ls)') to be replaced by a
call to `cd' using the arguments that were passed to the function."
  :type 'hook
  :group 'eshell-cmd)

(defcustom eshell-pre-rewrite-command-hook
  '(eshell-no-command-conversion
    eshell-subcommand-arg-values)
  "A hook run before command rewriting begins.
The terms of the command to be rewritten is passed as arguments, and
may be modified in place.  Any return value is ignored."
  :type 'hook
  :group 'eshell-cmd)

(defcustom eshell-rewrite-command-hook
  '(eshell-rewrite-for-command
    eshell-rewrite-while-command
    eshell-rewrite-if-command
    eshell-rewrite-sexp-command
    eshell-rewrite-initial-subcommand
    eshell-rewrite-named-command)
  "A set of functions used to rewrite the command argument.
Once parsing of a command line is completed, the next step is to
rewrite the initial argument into something runnable.

A module may wish to associate special behavior with certain argument
syntaxes at the beginning of a command line.  They are welcome to do
so by adding a function to this hook.  The first function to return a
substitute command form is the one used.  Each function is passed the
command's full argument list, which is a list of sexps (typically
forms or strings)."
  :type 'hook
  :group 'eshell-cmd)

(defvar eshell-post-rewrite-command-function #'identity
  "Function run after command rewriting is finished.
Takes the (rewritten) command, modifies it as it sees fit and returns
the new result to use instead.")
(defvar eshell-post-rewrite-command-hook nil
  "A hook run after command rewriting is finished.
Each function is passed the symbol containing the rewritten command,
which may be modified directly.  Any return value is ignored.")
(make-obsolete-variable 'eshell-post-rewrite-command-hook
                        'eshell-post-rewrite-command-function "24.4")

(defcustom eshell-complex-commands '("ls")
  "A list of commands names or functions, that determine complexity.
That is, if a command is defined by a function named eshell/NAME,
and NAME is part of this list, it is invoked as a complex command.
Complex commands are always correct, but run much slower.  If a
command works fine without being part of this list, then it doesn't
need to be.

If an entry is a function, it will be called with the name, and should
return non-nil if the command is complex."
  :type '(repeat :tag "Commands"
                 (choice (string :tag "Name")
                         (function :tag "Predicate")))
  :group 'eshell-cmd)

;;; User Variables:

(defcustom eshell-cmd-load-hook nil
  "A hook that gets run when `eshell-cmd' is loaded."
  :version "24.1"                      ; removed eshell-cmd-initialize
  :type 'hook
  :group 'eshell-cmd)

(defcustom eshell-debug-command nil
  "If non-nil, enable Eshell debugging code.
This is slow, and only useful for debugging problems with Eshell.
If you change this without using customize after Eshell has loaded,
you must re-load 'esh-cmd.el'."
  :initialize 'custom-initialize-default
  :set (lambda (symbol value)
         (set symbol value)
         (load-library "esh-cmd"))
  :type 'boolean
  :group 'eshell-cmd)

(defcustom eshell-deferrable-commands
  '(eshell-named-command
    eshell-lisp-command
    eshell-process-identity)
  "A list of functions which might return an asynchronous process.
If they return a process object, execution of the calling Eshell
command will wait for completion (in the background) before finishing
the command."
  :type '(repeat function)
  :group 'eshell-cmd)

(defcustom eshell-subcommand-bindings
  '((eshell-in-subcommand-p t)
    (default-directory default-directory)
    (process-environment (eshell-copy-environment)))
  "A list of `let' bindings for subcommand environments."
  :type 'sexp
  :group 'eshell-cmd)

(put 'risky-local-variable 'eshell-subcommand-bindings t)

(defvar eshell-ensure-newline-p nil
  "If non-nil, ensure that a newline is emitted after a Lisp form.
This can be changed by Lisp forms that are evaluated from the Eshell
command line.")

;;; Internal Variables:

(defvar eshell-current-command nil)
(defvar eshell-command-name nil)
(defvar eshell-command-arguments nil)
(defvar eshell-in-pipeline-p nil
  "Internal Eshell variable, non-nil inside a pipeline.
Has the value 'first, 'last for the first/last commands in the pipeline,
otherwise t.")
(defvar eshell-in-subcommand-p nil)
(defvar eshell-last-arguments nil)
(defvar eshell-last-command-name nil)
(defvar eshell-last-async-proc nil
  "When this foreground process completes, resume command evaluation.")

;;; Functions:

(defsubst eshell-interactive-process ()
  "Return currently running command process, if non-Lisp."
  eshell-last-async-proc)

(defun eshell-cmd-initialize ()
  "Initialize the Eshell command processing module."
  (set (make-local-variable 'eshell-current-command) nil)
  (set (make-local-variable 'eshell-command-name) nil)
  (set (make-local-variable 'eshell-command-arguments) nil)
  (set (make-local-variable 'eshell-last-arguments) nil)
  (set (make-local-variable 'eshell-last-command-name) nil)
  (set (make-local-variable 'eshell-last-async-proc) nil)

  (add-hook 'eshell-kill-hook 'eshell-resume-command nil t)

  ;; make sure that if a command is over, and no process is being
  ;; waited for, that `eshell-current-command' is set to nil.  This
  ;; situation can occur, for example, if a Lisp function results in
  ;; `debug' being called, and the user then types \\[top-level]
  (add-hook 'eshell-post-command-hook
            (function
             (lambda ()
               (setq eshell-current-command nil
                     eshell-last-async-proc nil))) nil t)

  (add-hook 'eshell-parse-argument-hook
            'eshell-parse-subcommand-argument nil t)
  (add-hook 'eshell-parse-argument-hook
            'eshell-parse-lisp-argument nil t)

  (when (eshell-using-module 'eshell-cmpl)
    (add-hook 'pcomplete-try-first-hook
              'eshell-complete-lisp-symbols nil t)))

(defun eshell-complete-lisp-symbols ()
  "If there is a user reference, complete it."
  (let ((arg (pcomplete-actual-arg)))
    (when (string-match (concat "\\`" eshell-lisp-regexp) arg)
      (setq pcomplete-stub (substring arg (match-end 0))
            pcomplete-last-completion-raw t)
      (throw 'pcomplete-completions
             (all-completions pcomplete-stub obarray 'boundp)))))

;; Command parsing

(defvar eshell--sep-terms)

(defun eshell-parse-command (command &optional args toplevel)
  "Parse the COMMAND, adding ARGS if given.
COMMAND can either be a string, or a cons cell demarcating a buffer
region.  TOPLEVEL, if non-nil, means that the outermost command (the
user's input command) is being parsed, and that pre and post command
hooks should be run before and after the command."
  (let* (eshell--sep-terms
         (terms
          (append
           (if (consp command)
               (eshell-parse-arguments (car command) (cdr command))
             (let ((here (point))
                   (inhibit-point-motion-hooks t))
               (with-silent-modifications
                 ;; FIXME: Why not use a temporary buffer and avoid this
                 ;; "insert&delete" business?  --Stef
                 (insert command)
                 (prog1
                     (eshell-parse-arguments here (point))
                   (delete-region here (point))))))
           args))
         (commands
          (mapcar
           (function
            (lambda (cmd)
              (setq cmd
                    (if (or (not (car eshell--sep-terms))
                            (string= (car eshell--sep-terms) ";"))
                        (eshell-parse-pipeline cmd)
                      `(eshell-do-subjob
                        (list ,(eshell-parse-pipeline cmd)))))
              (setq eshell--sep-terms (cdr eshell--sep-terms))
              (if eshell-in-pipeline-p
                  cmd
                `(eshell-trap-errors ,cmd))))
           (eshell-separate-commands terms "[&;]" nil 'eshell--sep-terms))))
    (let ((cmd commands))
      (while cmd
        (if (cdr cmd)
            (setcar cmd `(eshell-commands ,(car cmd))))
        (setq cmd (cdr cmd))))
    (if toplevel
        `(eshell-commands (progn
                            (run-hooks 'eshell-pre-command-hook)
                            (catch 'top-level (progn ,@commands))
                            (run-hooks 'eshell-post-command-hook)))
      (macroexp-progn commands))))

(defun eshell-debug-command (tag subform)
  "Output a debugging message to '*eshell last cmd*'."
  (let ((buf (get-buffer-create "*eshell last cmd*"))
        (text (eshell-stringify eshell-current-command)))
    (with-current-buffer buf
      (if (not tag)
          (erase-buffer)
        (insert "\n\C-l\n" tag "\n\n" text
                (if subform
                    (concat "\n\n" (eshell-stringify subform)) ""))))))

(defun eshell-debug-show-parsed-args (terms)
  "Display parsed arguments in the debug buffer."
  (ignore
   (if eshell-debug-command
       (eshell-debug-command "parsed arguments" terms))))

(defun eshell-no-command-conversion (terms)
  "Don't convert the command argument."
  (ignore
   (if (and (listp (car terms))
            (eq (caar terms) 'eshell-convert))
       (setcar terms (cadr (car terms))))))

(defun eshell-subcommand-arg-values (terms)
  "Convert subcommand arguments {x} to ${x}, in order to take their values."
  (setq terms (cdr terms))              ; skip command argument
  (while terms
    (if (and (listp (car terms))
             (eq (caar terms) 'eshell-as-subcommand))
        (setcar terms `(eshell-convert
                        (eshell-command-to-value ,(car terms)))))
    (setq terms (cdr terms))))

(defun eshell-rewrite-sexp-command (terms)
  "Rewrite a sexp in initial position, such as '(+ 1 2)'."
  ;; this occurs when a Lisp expression is in first position
  (if (and (listp (car terms))
           (eq (caar terms) 'eshell-command-to-value))
      (car (cdar terms))))

(defun eshell-rewrite-initial-subcommand (terms)
  "Rewrite a subcommand in initial position, such as '{+ 1 2}'."
  (if (and (listp (car terms))
           (eq (caar terms) 'eshell-as-subcommand))
      (car terms)))

(defun eshell-rewrite-named-command (terms)
  "If no other rewriting rule transforms TERMS, assume a named command."
  (let ((sym (if eshell-in-pipeline-p
                 'eshell-named-command*
               'eshell-named-command))
        (cmd (car terms))
        (args (cdr terms)))
    (if args
        (list sym cmd `(list ,@(cdr terms)))
      (list sym cmd))))

(defvar eshell-command-body)
(defvar eshell-test-body)

(defsubst eshell-invokify-arg (arg &optional share-output silent)
  "Change ARG so it can be invoked from a structured command.

SHARE-OUTPUT, if non-nil, means this invocation should share the
current output stream, which is separately redirectable.  SILENT
means the user and/or any redirections shouldn't see any output
from this command.  If both SHARE-OUTPUT and SILENT are non-nil,
the second is ignored."
  ;; something that begins with `eshell-convert' means that it
  ;; intends to return a Lisp value.  We want to get past this,
  ;; but if it's not _actually_ a value interpolation -- in which
  ;; we leave it alone.  In fact, the only time we muck with it
  ;; is in the case of a {subcommand} that has been turned into
  ;; the interpolation, ${subcommand}, by the parser because it
  ;; didn't know better.
  (if (and (listp arg)
           (eq (car arg) 'eshell-convert)
           (eq (car (cadr arg)) 'eshell-command-to-value))
      (if share-output
          (cadr (cadr arg))
        `(eshell-commands ,(cadr (cadr arg)) ,silent))
    arg))

(defvar eshell-last-command-status)     ;Define in esh-io.el.
(defvar eshell--local-vars nil
  "List of locally bound vars that should take precedence over env-vars.")

(defun eshell-rewrite-for-command (terms)
  "Rewrite a `for' command into its equivalent Eshell command form.
Because the implementation of `for' relies upon conditional evaluation
of its argument (i.e., use of a Lisp special form), it must be
implemented via rewriting, rather than as a function."
  (if (and (equal (car terms) "for")
           (equal (nth 2 terms) "in"))
      (let ((body (car (last terms))))
        (setcdr (last terms 2) nil)
        `(let ((for-items
                (copy-tree
                 (append
                  ,@(mapcar
                     (lambda (elem)
                       (if (listp elem)
                           elem
                         `(list ,elem)))
                     (cdr (cddr terms))))))
               (eshell-command-body '(nil))
               (eshell-test-body '(nil)))
           (while (car for-items)
             (let ((,(intern (cadr terms)) (car for-items))
                   (eshell--local-vars (cons ',(intern (cadr terms))
                                            eshell--local-vars)))
               (eshell-protect
                ,(eshell-invokify-arg body t)))
             (setcar for-items (cadr for-items))
             (setcdr for-items (cddr for-items)))
           (eshell-close-handles
            eshell-last-command-status
            (list 'quote eshell-last-command-result))))))

(defun eshell-structure-basic-command (func names keyword test body
                                            &optional else)
  "With TERMS, KEYWORD, and two NAMES, structure a basic command.
The first of NAMES should be the positive form, and the second the
negative.  It's not likely that users should ever need to call this
function."
  ;; If the test form begins with `eshell-convert', it means
  ;; something data-wise will be returned, and we should let
  ;; that determine the truth of the statement.
  (unless (eq (car test) 'eshell-convert)
    (setq test
          `(progn ,test
                  (eshell-exit-success-p))))

  ;; should we reverse the sense of the test?  This depends
  ;; on the `names' parameter.  If it's the symbol nil, yes.
  ;; Otherwise, it can be a pair of strings; if the keyword
  ;; we're using matches the second member of that pair (a
  ;; list), we should reverse it.
  (if (or (eq names nil)
          (and (listp names)
               (string= keyword (cadr names))))
      (setq test `(not ,test)))

  ;; finally, create the form that represents this structured
  ;; command
  `(let ((eshell-command-body '(nil))
         (eshell-test-body '(nil)))
     (,func ,test ,body ,else)
     (eshell-close-handles
        eshell-last-command-status
        (list 'quote eshell-last-command-result))))

(defun eshell-rewrite-while-command (terms)
  "Rewrite a `while' command into its equivalent Eshell command form.
Because the implementation of `while' relies upon conditional
evaluation of its argument (i.e., use of a Lisp special form), it
must be implemented via rewriting, rather than as a function."
  (if (and (stringp (car terms))
           (member (car terms) '("while" "until")))
      (eshell-structure-basic-command
       'while '("while" "until") (car terms)
       (eshell-invokify-arg (cadr terms) nil t)
       `(eshell-protect
         ,(eshell-invokify-arg (car (last terms)) t)))))

(defun eshell-rewrite-if-command (terms)
  "Rewrite an `if' command into its equivalent Eshell command form.
Because the implementation of `if' relies upon conditional
evaluation of its argument (i.e., use of a Lisp special form), it
must be implemented via rewriting, rather than as a function."
  (if (and (stringp (car terms))
           (member (car terms) '("if" "unless")))
      (eshell-structure-basic-command
       'if '("if" "unless") (car terms)
       (eshell-invokify-arg (cadr terms) nil t)
       `(eshell-protect
         ,(eshell-invokify-arg (car (last terms (if (= (length terms) 4) 2)))
                               t))
       (if (= (length terms) 4)
           `(eshell-protect
             ,(eshell-invokify-arg (car (last terms)))) t))))

(defvar eshell-last-command-result)     ;Defined in esh-io.el.

(defun eshell-exit-success-p ()
  "Return non-nil if the last command was \"successful\".
For a bit of Lisp code, this means a return value of non-nil.
For an external command, it means an exit code of 0."
  (if (save-match-data
        (string-match "#<\\(Lisp object\\|function .*\\)>"
                      eshell-last-command-name))
      eshell-last-command-result
    (= eshell-last-command-status 0)))

(defvar eshell--cmd)

(defun eshell-parse-pipeline (terms)
  "Parse a pipeline from TERMS, return the appropriate Lisp forms."
  (let* (eshell--sep-terms
         (bigpieces (eshell-separate-commands terms "\\(&&\\|||\\)"
                                              nil 'eshell--sep-terms))
         (bp bigpieces)
         (results (list t))
         final)
    (while bp
      (let ((subterms (car bp)))
        (let* ((pieces (eshell-separate-commands subterms "|"))
               (p pieces))
          (while p
            (let ((cmd (car p)))
              (run-hook-with-args 'eshell-pre-rewrite-command-hook cmd)
              (setq cmd (run-hook-with-args-until-success
                         'eshell-rewrite-command-hook cmd))
              (let ((eshell--cmd cmd))
                (run-hook-with-args 'eshell-post-rewrite-command-hook
                                    'eshell--cmd)
                (setq cmd eshell--cmd))
              (setcar p (funcall eshell-post-rewrite-command-function cmd)))
            (setq p (cdr p)))
          (nconc results
                 (list
                  (if (<= (length pieces) 1)
                      (car pieces)
                    (cl-assert (not eshell-in-pipeline-p))
                    `(eshell-execute-pipeline (quote ,pieces))))))
        (setq bp (cdr bp))))
    ;; `results' might be empty; this happens in the case of
    ;; multi-line input
    (setq results (cdr results)
          results (nreverse results)
          final (car results)
          results (cdr results)
          eshell--sep-terms (nreverse eshell--sep-terms))
    (while results
      (cl-assert (car eshell--sep-terms))
      (setq final (eshell-structure-basic-command
                   'if (string= (car eshell--sep-terms) "&&") "if"
                   `(eshell-protect ,(car results))
                   `(eshell-protect ,final))
            results (cdr results)
            eshell--sep-terms (cdr eshell--sep-terms)))
    final))

(defun eshell-parse-subcommand-argument ()
  "Parse a subcommand argument of the form '{command}'."
  (if (and (not eshell-current-argument)
           (not eshell-current-quoted)
           (eq (char-after) ?\{)
           (or (= (point-max) (1+ (point)))
               (not (eq (char-after (1+ (point))) ?\}))))
      (let ((end (eshell-find-delimiter ?\{ ?\})))
        (if (not end)
            (throw 'eshell-incomplete ?\{)
          (when (eshell-arg-delimiter (1+ end))
            (prog1
                `(eshell-as-subcommand
                  ,(eshell-parse-command (cons (1+ (point)) end)))
              (goto-char (1+ end))))))))

(defun eshell-parse-lisp-argument ()
  "Parse a Lisp expression which is specified as an argument."
  (if (and (not eshell-current-argument)
           (not eshell-current-quoted)
           (looking-at eshell-lisp-regexp))
      (let* ((here (point))
             (obj
              (condition-case nil
                  (read (current-buffer))
                (end-of-file
                 (throw 'eshell-incomplete ?\()))))
        (if (eshell-arg-delimiter)
            `(eshell-command-to-value
              (eshell-lisp-command (quote ,obj)))
          (ignore (goto-char here))))))

(defun eshell-separate-commands (terms separator &optional
                                       reversed last-terms-sym)
  "Separate TERMS using SEPARATOR.
If REVERSED is non-nil, the list of separated term groups will be
returned in reverse order.  If LAST-TERMS-SYM is a symbol, its value
will be set to a list of all the separator operators found (or '(list
nil)' if none)."
  (let ((sub-terms (list t))
        (eshell-sep-terms (list t))
        subchains)
    (while terms
      (if (and (consp (car terms))
               (eq (caar terms) 'eshell-operator)
               (string-match (concat "^" separator "$")
                             (nth 1 (car terms))))
          (progn
            (nconc eshell-sep-terms (list (nth 1 (car terms))))
            (setq subchains (cons (cdr sub-terms) subchains)
                  sub-terms (list t)))
        (nconc sub-terms (list (car terms))))
      (setq terms (cdr terms)))
    (if (> (length sub-terms) 1)
        (setq subchains (cons (cdr sub-terms) subchains)))
    (if reversed
        (progn
          (if last-terms-sym
              (set last-terms-sym (reverse (cdr eshell-sep-terms))))
          subchains)                    ; already reversed
      (if last-terms-sym
          (set last-terms-sym (cdr eshell-sep-terms)))
      (nreverse subchains))))

;;_* Command evaluation macros
;;
;; The structure of the following macros is very important to
;; `eshell-do-eval' [Iterative evaluation]:
;;
;; @ Don't use forms that conditionally evaluate their arguments, such
;;   as `setq', `if', `while', `let*', etc.  The only special forms
;;   that can be used are `let', `condition-case' and
;;   `unwind-protect'.
;;
;; @ The main body of a `let' can contain only one form.  Use `progn'
;;   if necessary.
;;
;; @ The two `special' variables are `eshell-current-handles' and
;;   `eshell-current-subjob-p'.  Bind them locally with a `let' if you
;;   need to change them.  Change them directly only if your intention
;;   is to change the calling environment.

(defmacro eshell-do-subjob (object)
  "Evaluate a command OBJECT as a subjob.
We indicate that the process was run in the background by returning it
ensconced in a list."
  `(let ((eshell-current-subjob-p t))
     ,object))

(defmacro eshell-commands (object &optional silent)
  "Place a valid set of handles, and context, around command OBJECT."
  `(let ((eshell-current-handles
          (eshell-create-handles ,(not silent) 'append))
         eshell-current-subjob-p)
     ,object))

(defmacro eshell-trap-errors (object)
  "Trap any errors that occur, so they are not entirely fatal.
Also, the variable `eshell-this-command-hook' is available for the
duration of OBJECT's evaluation.  Note that functions should be added
to this hook using `nconc', and *not* `add-hook'.

Someday, when Scheme will become the dominant Emacs language, all of
this grossness will be made to disappear by using `call/cc'..."
  `(let ((eshell-this-command-hook '(ignore)))
     (eshell-condition-case err
         (prog1
             ,object
           (run-hooks 'eshell-this-command-hook))
       (error
        (run-hooks 'eshell-this-command-hook)
        (eshell-errorn (error-message-string err))
        (eshell-close-handles 1)))))

(defvar eshell-output-handle)           ;Defined in esh-io.el.
(defvar eshell-error-handle)            ;Defined in esh-io.el.

(defmacro eshell-copy-handles (object)
  "Duplicate current I/O handles, so OBJECT works with its own copy."
  `(let ((eshell-current-handles
          (eshell-create-handles
           (car (aref eshell-current-handles
                      eshell-output-handle)) nil
           (car (aref eshell-current-handles
                      eshell-error-handle)) nil)))
     ,object))

(defmacro eshell-protect (object)
  "Protect I/O handles, so they aren't get closed after eval'ing OBJECT."
  `(progn
     (eshell-protect-handles eshell-current-handles)
     ,object))

(defmacro eshell-do-pipelines (pipeline &optional notfirst)
  "Execute the commands in PIPELINE, connecting each to one another.
This macro calls itself recursively, with NOTFIRST non-nil."
  (when (setq pipeline (cadr pipeline))
    `(eshell-copy-handles
      (progn
        ,(when (cdr pipeline)
           `(let ((nextproc
                   (eshell-do-pipelines (quote ,(cdr pipeline)) t)))
              (eshell-set-output-handle ,eshell-output-handle
                                        'append nextproc)
              (eshell-set-output-handle ,eshell-error-handle
                                        'append nextproc)
              (setq tailproc (or tailproc nextproc))))
        ,(let ((head (car pipeline)))
           (if (memq (car head) '(let progn))
               (setq head (car (last head))))
           (when (memq (car head) eshell-deferrable-commands)
             (ignore
              (setcar head
                      (intern-soft
                       (concat (symbol-name (car head)) "*"))))))
        ;; First and last elements in a pipeline may need special treatment.
        ;; (Currently only eshell-ls-files uses 'last.)
        ;; Affects process-connection-type in eshell-gather-process-output.
        (let ((eshell-in-pipeline-p
               ,(cond ((not notfirst) (quote 'first))
                      ((cdr pipeline) t)
                      (t (quote 'last)))))
          ,(car pipeline))))))

(defmacro eshell-do-pipelines-synchronously (pipeline)
  "Execute the commands in PIPELINE in sequence synchronously.
Output of each command is passed as input to the next one in the pipeline.
This is used on systems where `start-process' is not supported."
  (when (setq pipeline (cadr pipeline))
    `(progn
       ,(when (cdr pipeline)
          `(let ((output-marker ,(point-marker)))
             (eshell-set-output-handle ,eshell-output-handle
                                       'append output-marker)
             (eshell-set-output-handle ,eshell-error-handle
                                       'append output-marker)))
       ,(let ((head (car pipeline)))
          (if (memq (car head) '(let progn))
              (setq head (car (last head))))
          ;; FIXME: is deferrable significant here?
          (when (memq (car head) eshell-deferrable-commands)
            (ignore
             (setcar head
                     (intern-soft
                      (concat (symbol-name (car head)) "*"))))))
       ;; The last process in the pipe should get its handles
       ;; redirected as we found them before running the pipe.
       ,(if (null (cdr pipeline))
            `(progn
               (setq eshell-current-handles tail-handles)
               (setq eshell-in-pipeline-p nil)))
       (let ((result ,(car pipeline)))
         ;; tailproc gets the result of the last successful process in
         ;; the pipeline.
         (setq tailproc (or result tailproc))
         ,(if (cdr pipeline)
              `(eshell-do-pipelines-synchronously (quote ,(cdr pipeline))))
         result))))

(defalias 'eshell-process-identity 'identity)

(defmacro eshell-execute-pipeline (pipeline)
  "Execute the commands in PIPELINE, connecting each to one another."
  `(let ((eshell-in-pipeline-p t) tailproc)
     (progn
       ,(if (fboundp 'start-process)
            `(eshell-do-pipelines ,pipeline)
          `(let ((tail-handles (eshell-create-handles
                                (car (aref eshell-current-handles
                                           ,eshell-output-handle)) nil
                                (car (aref eshell-current-handles
                                           ,eshell-error-handle)) nil)))
             (eshell-do-pipelines-synchronously ,pipeline)))
       (eshell-process-identity tailproc))))

(defmacro eshell-as-subcommand (command)
  "Execute COMMAND using a temp buffer.
This is used so that certain Lisp commands, such as `cd', when
executed in a subshell, do not disturb the environment of the main
Eshell buffer."
  `(let ,eshell-subcommand-bindings
     ,command))

(defmacro eshell-do-command-to-value (object)
  "Run a subcommand prepared by `eshell-command-to-value'.
This avoids the need to use `let*'."
  `(let ((eshell-current-handles
          (eshell-create-handles value 'overwrite)))
     (progn
       ,object
       (symbol-value value))))

(defmacro eshell-command-to-value (object)
  "Run OBJECT synchronously, returning its result as a string.
Returns a string comprising the output from the command."
  `(let ((value (make-symbol "eshell-temp")))
     (eshell-do-command-to-value ,object)))

;;;_* Iterative evaluation
;;
;; Eshell runs all of its external commands asynchronously, so that
;; Emacs is not blocked while the operation is being performed.
;; However, this introduces certain synchronization difficulties,
;; since the Lisp code, once it returns, will not "go back" to finish
;; executing the commands which haven't yet been started.
;;
;; What Eshell does to work around this problem (basically, the lack
;; of threads in Lisp), is that it evaluates the command sequence
;; iteratively.  Whenever an asynchronous process is begun, evaluation
;; terminates and control is given back to Emacs.  When that process
;; finishes, it will resume the evaluation using the remainder of the
;; command tree.

(defun eshell/eshell-debug (&rest args)
  "A command for toggling certain debug variables."
  (ignore
   (cond
    ((not args)
     (if eshell-handle-errors
         (eshell-print "errors\n"))
     (if eshell-debug-command
         (eshell-print "commands\n")))
    ((member (car args) '("-h" "--help"))
     (eshell-print "usage: eshell-debug [kinds]

This command is used to aid in debugging problems related to Eshell
itself.  It is not useful for anything else.  The recognized `kinds'
at the moment are:

  errors       stops Eshell from trapping errors
  commands     shows command execution progress in `*eshell last cmd*'
"))
    (t
     (while args
       (cond
        ((string= (car args) "errors")
         (setq eshell-handle-errors (not eshell-handle-errors)))
        ((string= (car args) "commands")
         (setq eshell-debug-command (not eshell-debug-command))))
       (setq args (cdr args)))))))

(defun pcomplete/eshell-mode/eshell-debug ()
  "Completion for the `debug' command."
  (while (pcomplete-here '("errors" "commands"))))

(defun eshell-invoke-directly (command)
  (let ((base (cadr (nth 2 (nth 2 (cadr command))))) name)
    (if (and (eq (car base) 'eshell-trap-errors)
             (eq (car (cadr base)) 'eshell-named-command))
        (setq name (cadr (cadr base))))
    (and name (stringp name)
         (not (member name eshell-complex-commands))
         (catch 'simple
           (progn
            (dolist (pred eshell-complex-commands)
              (if (and (functionp pred)
                       (funcall pred name))
                  (throw 'simple nil)))
            t))
         (fboundp (intern-soft (concat "eshell/" name))))))

(defun eshell-eval-command (command &optional input)
  "Evaluate the given COMMAND iteratively."
  (if eshell-current-command
      ;; we can just stick the new command at the end of the current
      ;; one, and everything will happen as it should
      (setcdr (last (cdr eshell-current-command))
              (list `(let ((here (and (eobp) (point))))
                       ,(and input
                             `(insert-and-inherit ,(concat input "\n")))
                       (if here
                           (eshell-update-markers here))
                       (eshell-do-eval ',command))))
    (and eshell-debug-command
         (with-current-buffer (get-buffer-create "*eshell last cmd*")
           (erase-buffer)
           (insert "command: \"" input "\"\n")))
    (setq eshell-current-command command)
    (let ((delim (catch 'eshell-incomplete
                   (eshell-resume-eval))))
      ;; On systems that don't support async subprocesses, eshell-resume
      ;; can return t.  Don't treat that as an error.
      (if (listp delim)
          (setq delim (car delim)))
      (if (and delim (not (eq delim t)))
          (error "Unmatched delimiter: %c" delim)))))

(defun eshell-resume-command (proc status)
  "Resume the current command when a process ends."
  (when proc
    (unless (or (not (stringp status))
                (string= "stopped" status)
                (string-match eshell-reset-signals status))
      (if (eq proc (eshell-interactive-process))
          (eshell-resume-eval)))))

(defun eshell-resume-eval ()
  "Destructively evaluate a form which may need to be deferred."
  (eshell-condition-case err
      (progn
        (setq eshell-last-async-proc nil)
        (when eshell-current-command
          (let* (retval
                 (proc (catch 'eshell-defer
                         (ignore
                          (setq retval
                                (eshell-do-eval
                                 eshell-current-command))))))
            (if (eshell-processp proc)
                (ignore (setq eshell-last-async-proc proc))
              (cadr retval)))))
    (error
     (error (error-message-string err)))))

(defmacro eshell-manipulate (tag &rest commands)
  "Manipulate a COMMAND form, with TAG as a debug identifier."
  (declare (indent 1))
  ;; Check `bound'ness since at compile time the code until here has not
  ;; executed yet.
  (if (not (and (boundp 'eshell-debug-command) eshell-debug-command))
      `(progn ,@commands)
    `(progn
       (eshell-debug-command ,(eval tag) form)
       ,@commands
       (eshell-debug-command ,(concat "done " (eval tag)) form))))

(defun eshell-do-eval (form &optional synchronous-p)
  "Evaluate form, simplifying it as we go.
Unless SYNCHRONOUS-P is non-nil, throws `eshell-defer' if it needs to
be finished later after the completion of an asynchronous subprocess."
  (cond
   ((not (listp form))
    (list 'quote (eval form)))
   ((memq (car form) '(quote function))
    form)
   (t
    ;; skip past the call to `eshell-do-eval'
    (when (eq (car form) 'eshell-do-eval)
      (setq form (cadr (cadr form))))
    ;; expand any macros directly into the form.  This is done so that
    ;; we can modify any `let' forms to evaluate only once.
    (if (macrop (car form))
        (let ((exp (eshell-copy-tree (macroexpand form))))
          (eshell-manipulate (format "expanding macro `%s'"
                                     (symbol-name (car form)))
            (setcar form (car exp))
            (setcdr form (cdr exp)))))
    (let ((args (cdr form)))
      (cond
       ((eq (car form) 'while)
        ;; `eshell-copy-tree' is needed here so that the test argument
        ;; doesn't get modified and thus always yield the same result.
        (when (car eshell-command-body)
          (cl-assert (not synchronous-p))
          (eshell-do-eval (car eshell-command-body))
          (setcar eshell-command-body nil)
          (setcar eshell-test-body nil))
        (unless (car eshell-test-body)
          (setcar eshell-test-body (eshell-copy-tree (car args))))
        (while (cadr (eshell-do-eval (car eshell-test-body)))
          (setcar eshell-command-body
                  (if (cddr args)
                      `(progn ,@(eshell-copy-tree (cdr args)))
                    (eshell-copy-tree (cadr args))))
          (eshell-do-eval (car eshell-command-body) synchronous-p)
          (setcar eshell-command-body nil)
          (setcar eshell-test-body (eshell-copy-tree (car args))))
        (setcar eshell-command-body nil))
       ((eq (car form) 'if)
        ;; `eshell-copy-tree' is needed here so that the test argument
        ;; doesn't get modified and thus always yield the same result.
        (if (car eshell-command-body)
            (progn
              (cl-assert (not synchronous-p))
              (eshell-do-eval (car eshell-command-body)))
          (unless (car eshell-test-body)
            (setcar eshell-test-body (eshell-copy-tree (car args))))
          (setcar eshell-command-body
                  (eshell-copy-tree
                   (if (cadr (eshell-do-eval (car eshell-test-body)))
                       (cadr args)
                     (car (cddr args)))))
          (eshell-do-eval (car eshell-command-body) synchronous-p))
        (setcar eshell-command-body nil)
        (setcar eshell-test-body nil))
       ((eq (car form) 'setcar)
        (setcar (cdr args) (eshell-do-eval (cadr args) synchronous-p))
        (eval form))
       ((eq (car form) 'setcdr)
        (setcar (cdr args) (eshell-do-eval (cadr args) synchronous-p))
        (eval form))
       ((memq (car form) '(let catch condition-case unwind-protect))
        ;; `let', `condition-case' and `unwind-protect' have to be
        ;; handled specially, because we only want to call
        ;; `eshell-do-eval' on their first form.
        ;;
        ;; NOTE: This requires obedience by all forms which this
        ;; function might encounter, that they do not contain
        ;; other special forms.
        (if (and (eq (car form) 'let)
                 (not (eq (car (cadr args)) 'eshell-do-eval)))
            (eshell-manipulate "evaluating let args"
              (dolist (letarg (car args))
                (if (and (listp letarg)
                         (not (eq (cadr letarg) 'quote)))
                    (setcdr letarg
                            (list (eshell-do-eval
                                   (cadr letarg) synchronous-p)))))))
        (unless (eq (car form) 'unwind-protect)
          (setq args (cdr args)))
        (unless (eq (caar args) 'eshell-do-eval)
          (eshell-manipulate "handling special form"
            (setcar args `(eshell-do-eval ',(car args) ,synchronous-p))))
        (eval form))
       ((eq (car form) 'setq)
        (if (cddr args) (error "Unsupported form (setq X1 E1 X2 E2..)"))
        (eshell-manipulate "evaluating arguments to setq"
          (setcar (cdr args) (eshell-do-eval (cadr args) synchronous-p)))
        (list 'quote (eval form)))
       (t
        (if (and args (not (memq (car form) '(run-hooks))))
            (eshell-manipulate
                (format "evaluating arguments to `%s'"
                        (symbol-name (car form)))
              (while args
                (setcar args (eshell-do-eval (car args) synchronous-p))
                (setq args (cdr args)))))
        (cond
         ((eq (car form) 'progn)
          (car (last form)))
         ((eq (car form) 'prog1)
          (cadr form))
         (t
          ;; If a command desire to replace its execution form with
          ;; another command form, all it needs to do is throw the new
          ;; form using the exception tag `eshell-replace-command'.
          ;; For example, let's say that the form currently being
          ;; eval'd is:
          ;;
          ;;   (eshell-named-command "hello")
          ;;
          ;; Now, let's assume the 'hello' command is an Eshell alias,
          ;; the definition of which yields the command:
          ;;
          ;;   (eshell-named-command "echo" (list "Hello" "world"))
          ;;
          ;; What the alias code would like to do is simply substitute
          ;; the alias form for the original form.  To accomplish
          ;; this, all it needs to do is to throw the substitution
          ;; form with the `eshell-replace-command' tag, and the form
          ;; will be replaced within the current command, and
          ;; execution will then resume (iteratively) as before.
          ;; Thus, aliases can even contain references to asynchronous
          ;; sub-commands, and things will still work out as they
          ;; should.
          (let* (result
                 (new-form
                  (catch 'eshell-replace-command
                    (ignore
                     (setq result (eval form))))))
            (if new-form
                (progn
                  (eshell-manipulate "substituting replacement form"
                    (setcar form (car new-form))
                    (setcdr form (cdr new-form)))
                  (eshell-do-eval form synchronous-p))
              (if (and (memq (car form) eshell-deferrable-commands)
                       (not eshell-current-subjob-p)
                       result
                       (eshell-processp result))
                  (if synchronous-p
                      (eshell/wait result)
                    (eshell-manipulate "inserting ignore form"
                      (setcar form 'ignore)
                      (setcdr form nil))
                    (throw 'eshell-defer result))
                (list 'quote result))))))))))))

;; command invocation

(defun eshell/which (command &rest names)
  "Identify the COMMAND, and where it is located."
  (dolist (name (cons command names))
    (let (program alias direct)
      (if (eq (aref name 0) eshell-explicit-command-char)
          (setq name (substring name 1)
                direct t))
      (if (and (not direct)
               (eshell-using-module 'eshell-alias)
               (setq alias
                     (funcall (symbol-function 'eshell-lookup-alias)
                              name)))
          (setq program
                (concat name " is an alias, defined as \""
                        (cadr alias) "\"")))
      (unless program
        (setq program (eshell-search-path name))
        (let* ((esym (eshell-find-alias-function name))
               (sym (or esym (intern-soft name))))
          (if (and (or esym (and sym (fboundp sym)))
                   (or eshell-prefer-lisp-functions (not direct)))
              (let ((desc (let ((inhibit-redisplay t))
                            (save-window-excursion
                              (prog1
                                  (describe-function sym)
                                (message nil))))))
                (setq desc (if desc (substring desc 0
                                               (1- (or (string-match "\n" desc)
                                                       (length desc))))
                             ;; This should not happen.
                             (format "%s is defined, \
but no documentation was found" name)))
                (if (buffer-live-p (get-buffer "*Help*"))
                    (kill-buffer "*Help*"))
                (setq program (or desc name))))))
      (if (not program)
          (eshell-error (format "which: no %s in (%s)\n"
                                name (getenv "PATH")))
        (eshell-printn program)))))

(put 'eshell/which 'eshell-no-numeric-conversions t)

(defun eshell-named-command (command &optional args)
  "Insert output from a plain COMMAND, using ARGS.
COMMAND may result in an alias being executed, or a plain command."
  (setq eshell-last-arguments args
        eshell-last-command-name (eshell-stringify command))
  (run-hook-with-args 'eshell-prepare-command-hook)
  (cl-assert (stringp eshell-last-command-name))
  (if eshell-last-command-name
      (or (run-hook-with-args-until-success
           'eshell-named-command-hook eshell-last-command-name
           eshell-last-arguments)
          (eshell-plain-command eshell-last-command-name
                                eshell-last-arguments))))

(defalias 'eshell-named-command* 'eshell-named-command)

(defun eshell-find-alias-function (name)
  "Check whether a function called `eshell/NAME' exists."
  (let* ((sym (intern-soft (concat "eshell/" name)))
         (file (symbol-file sym 'defun)))
    ;; If the function exists, but is defined in an eshell module
    ;; that's not currently enabled, don't report it as found.
    (if (and file
             (setq file (file-name-base file))
             (string-match "\\`\\(em\\|esh\\)-\\([[:alnum:]]+\\)\\'" file))
        (let ((module-sym
               (intern (concat "eshell-" (match-string 2 file)))))
          (if (and (functionp sym)
                   (or (null module-sym)
                       (eshell-using-module module-sym)
                       (memq module-sym (eshell-subgroups 'eshell))))
              sym))
      ;; Otherwise, if it's bound, return it.
      (if (functionp sym)
          sym))))

(defun eshell-plain-command (command args)
  "Insert output from a plain COMMAND, using ARGS.
COMMAND may result in either a Lisp function being executed by name,
or an external command."
  (let* ((esym (eshell-find-alias-function command))
         (sym (or esym (intern-soft command))))
    (if (and sym (fboundp sym)
             (or esym eshell-prefer-lisp-functions
                 (not (eshell-search-path command))))
        (eshell-lisp-command sym args)
      (eshell-external-command command args))))

(defun eshell-exec-lisp (printer errprint func-or-form args form-p)
  "Execute a lisp FUNC-OR-FORM, maybe passing ARGS.
PRINTER and ERRPRINT are functions to use for printing regular
messages, and errors.  FORM-P should be non-nil if FUNC-OR-FORM
represent a lisp form; ARGS will be ignored in that case."
  (eshell-condition-case err
      (let ((result
             (save-current-buffer
               (if form-p
                   (eval func-or-form)
                 (apply func-or-form args)))))
        (and result (funcall printer result))
        result)
    (error
     (let ((msg (error-message-string err)))
       (if (and (not form-p)
                (string-match "^Wrong number of arguments" msg)
                (fboundp 'eldoc-get-fnsym-args-string))
           (let ((func-doc (eldoc-get-fnsym-args-string func-or-form)))
             (setq msg (format "usage: %s" func-doc))))
       (funcall errprint msg))
     nil)))

(defsubst eshell-apply* (printer errprint func args)
  "Call FUNC, with ARGS, trapping errors and return them as output.
PRINTER and ERRPRINT are functions to use for printing regular
messages, and errors."
  (eshell-exec-lisp printer errprint func args nil))

(defsubst eshell-funcall* (printer errprint func &rest args)
  "Call FUNC, with ARGS, trapping errors and return them as output."
  (eshell-apply* printer errprint func args))

(defsubst eshell-eval* (printer errprint form)
  "Evaluate FORM, trapping errors and returning them."
  (eshell-exec-lisp printer errprint form nil t))

(defsubst eshell-apply (func args)
  "Call FUNC, with ARGS, trapping errors and return them as output.
PRINTER and ERRPRINT are functions to use for printing regular
messages, and errors."
  (eshell-apply* 'eshell-print 'eshell-error func args))

(defsubst eshell-funcall (func &rest args)
  "Call FUNC, with ARGS, trapping errors and return them as output."
  (eshell-apply func args))

(defsubst eshell-eval (form)
  "Evaluate FORM, trapping errors and returning them."
  (eshell-eval* 'eshell-print 'eshell-error form))

(defsubst eshell-applyn (func args)
  "Call FUNC, with ARGS, trapping errors and return them as output.
PRINTER and ERRPRINT are functions to use for printing regular
messages, and errors."
  (eshell-apply* 'eshell-printn 'eshell-errorn func args))

(defsubst eshell-funcalln (func &rest args)
  "Call FUNC, with ARGS, trapping errors and return them as output."
  (eshell-applyn func args))

(defsubst eshell-evaln (form)
  "Evaluate FORM, trapping errors and returning them."
  (eshell-eval* 'eshell-printn 'eshell-errorn form))

(defvar eshell-last-output-end)         ;Defined in esh-mode.el.

(defun eshell-lisp-command (object &optional args)
  "Insert Lisp OBJECT, using ARGS if a function."
  (catch 'eshell-external               ; deferred to an external command
    (let* ((eshell-ensure-newline-p (eshell-interactive-output-p))
           (result
            (if (functionp object)
                (progn
                  (setq eshell-last-arguments args
                        eshell-last-command-name
                        (concat "#<function " (symbol-name object) ">"))
                  ;; if any of the arguments are flagged as numbers
                  ;; waiting for conversion, convert them now
                  (unless (get object 'eshell-no-numeric-conversions)
                    (while args
                      (let ((arg (car args)))
                        (if (and (stringp arg)
                                 (> (length arg) 0)
                                 (not (text-property-not-all
                                       0 (length arg) 'number t arg)))
                            (setcar args (string-to-number arg))))
                      (setq args (cdr args))))
                  (eshell-apply object eshell-last-arguments))
              (setq eshell-last-arguments args
                    eshell-last-command-name "#<Lisp object>")
              (eshell-eval object))))
      (if (and eshell-ensure-newline-p
               (save-excursion
                 (goto-char eshell-last-output-end)
                 (not (bolp))))
          (eshell-print "\n"))
      (eshell-close-handles 0 (list 'quote result)))))

(provide 'esh-cmd)

(provide 'esh-mode)

(require 'esh-util)
(require 'esh-module)
(require 'esh-cmd)
(require 'esh-io)
(require 'esh-var)

(defgroup eshell-mode nil
  "This module contains code for handling input from the user."
  :tag "User interface"
  :group 'eshell)

;;; User Variables:

(defcustom eshell-mode-unload-hook nil
  "A hook that gets run when `eshell-mode' is unloaded."
  :type 'hook
  :group 'eshell-mode)

(defcustom eshell-mode-hook nil
  "A hook that gets run when `eshell-mode' is entered."
  :type 'hook
  :group 'eshell-mode)

(defcustom eshell-first-time-mode-hook nil
  "A hook that gets run the first time `eshell-mode' is entered.
That is to say, the first time during an Emacs session."
  :type 'hook
  :group 'eshell-mode)

(defcustom eshell-exit-hook nil
  "A hook that is run whenever `eshell' is exited.
This hook is only run if exiting actually kills the buffer."
  :version "24.1"                       ; removed eshell-query-kill-processes
  :type 'hook
  :group 'eshell-mode)

(defcustom eshell-kill-on-exit t
  "If non-nil, kill the Eshell buffer on the `exit' command.
Otherwise, the buffer will simply be buried."
  :type 'boolean
  :group 'eshell-mode)

(defcustom eshell-input-filter-functions nil
  "Functions to call before input is processed.
The input is contained in the region from `eshell-last-input-start' to
`eshell-last-input-end'."
  :type 'hook
  :group 'eshell-mode)

(defcustom eshell-send-direct-to-subprocesses nil
  "If t, send any input immediately to a subprocess."
  :type 'boolean
  :group 'eshell-mode)

(defcustom eshell-expand-input-functions nil
  "Functions to call before input is parsed.
Each function is passed two arguments, which bounds the region of the
current input text."
  :type 'hook
  :group 'eshell-mode)

(defcustom eshell-scroll-to-bottom-on-input nil
  "Controls whether input to interpreter causes window to scroll.
If nil, then do not scroll.  If t or `all', scroll all windows showing
buffer.  If `this', scroll only the selected window.

See `eshell-preinput-scroll-to-bottom'."
  :type '(radio (const :tag "Do not scroll Eshell windows" nil)
                (const :tag "Scroll all windows showing the buffer" all)
                (const :tag "Scroll only the selected window" this))
  :group 'eshell-mode)

(defcustom eshell-scroll-to-bottom-on-output nil
  "Controls whether interpreter output causes window to scroll.
If nil, then do not scroll.  If t or `all', scroll all windows showing
buffer.  If `this', scroll only the selected window.  If `others',
scroll only those that are not the selected window.

See variable `eshell-scroll-show-maximum-output' and function
`eshell-postoutput-scroll-to-bottom'."
  :type '(radio (const :tag "Do not scroll Eshell windows" nil)
                (const :tag "Scroll all windows showing the buffer" all)
                (const :tag "Scroll only the selected window" this)
                (const :tag "Scroll all windows other than selected" this))
  :group 'eshell-mode)

(defcustom eshell-scroll-show-maximum-output t
  "Controls how interpreter output causes window to scroll.
If non-nil, then show the maximum output when the window is scrolled.

See variable `eshell-scroll-to-bottom-on-output' and function
`eshell-postoutput-scroll-to-bottom'."
  :type 'boolean
  :group 'eshell-mode)

(defcustom eshell-buffer-maximum-lines 1024
  "The maximum size in lines for eshell buffers.
Eshell buffers are truncated from the top to be no greater than this
number, if the function `eshell-truncate-buffer' is on
`eshell-output-filter-functions'."
  :type 'integer
  :group 'eshell-mode)

(defcustom eshell-output-filter-functions
  '(eshell-postoutput-scroll-to-bottom
    eshell-handle-control-codes
    eshell-handle-ansi-color
    eshell-watch-for-password-prompt)
  "Functions to call before output is displayed.
These functions are only called for output that is displayed
interactively, and not for output which is redirected."
  :type 'hook
  :group 'eshell-mode)

(defcustom eshell-preoutput-filter-functions nil
  "Functions to call before output is inserted into the buffer.
These functions get one argument, a string containing the text to be
inserted.  They return the string as it should be inserted."
  :type 'hook
  :group 'eshell-mode)

(defcustom eshell-password-prompt-regexp
  (format "\\(%s\\).*:\\s *\\'" (regexp-opt password-word-equivalents))
  "Regexp matching prompts for passwords in the inferior process.
This is used by `eshell-watch-for-password-prompt'."
  :type 'regexp
  :group 'eshell-mode)

(defcustom eshell-skip-prompt-function nil
  "A function called from beginning of line to skip the prompt."
  :type '(choice (const nil) function)
  :group 'eshell-mode)

(define-obsolete-variable-alias 'eshell-status-in-modeline
  'eshell-status-in-mode-line "24.3")

(defcustom eshell-status-in-mode-line t
  "If non-nil, let the user know a command is running in the mode line."
  :type 'boolean
  :group 'eshell-mode)

(defvar eshell-first-time-p t
  "A variable which is non-nil the first time Eshell is loaded.")

;; Internal Variables:

;; these are only set to `nil' initially for the sake of the
;; byte-compiler, when compiling other files which `require' this one
(defvar eshell-mode nil)
(defvar eshell-mode-map nil)
(defvar eshell-command-running-string "--")
(defvar eshell-command-map nil)
(defvar eshell-command-prefix nil)
(defvar eshell-last-input-start nil)
(defvar eshell-last-input-end nil)
(defvar eshell-last-output-start nil)
(defvar eshell-last-output-block-begin nil)
(defvar eshell-last-output-end nil)

(defvar eshell-currently-handling-window nil)

(define-abbrev-table 'eshell-mode-abbrev-table ())

(defvar eshell-mode-syntax-table
  (let ((st (make-syntax-table))
        (i 0))
    (while (< i ?0)
      (modify-syntax-entry i "_   " st)
      (setq i (1+ i)))
    (setq i (1+ ?9))
    (while (< i ?A)
      (modify-syntax-entry i "_   " st)
      (setq i (1+ i)))
    (setq i (1+ ?Z))
    (while (< i ?a)
      (modify-syntax-entry i "_   " st)
      (setq i (1+ i)))
    (setq i (1+ ?z))
    (while (< i 128)
      (modify-syntax-entry i "_   " st)
      (setq i (1+ i)))
    (modify-syntax-entry ?  "    " st)
    (modify-syntax-entry ?\t "    " st)
    (modify-syntax-entry ?\f "    " st)
    (modify-syntax-entry ?\n ">   " st)
    ;; Give CR the same syntax as newline, for selective-display.
    (modify-syntax-entry ?\^m ">   " st)
    ;; (modify-syntax-entry ?\; "<   " st)
    (modify-syntax-entry ?` "'   " st)
    (modify-syntax-entry ?' "'   " st)
    (modify-syntax-entry ?, "'   " st)
    ;; Used to be singlequote; changed for flonums.
    (modify-syntax-entry ?. "_   " st)
    (modify-syntax-entry ?- "_   " st)
    (modify-syntax-entry ?| ".   " st)
    (modify-syntax-entry ?# "'   " st)
    (modify-syntax-entry ?\" "\"    " st)
    (modify-syntax-entry ?\\ "/   " st)
    (modify-syntax-entry ?\( "()  " st)
    (modify-syntax-entry ?\) ")(  " st)
    (modify-syntax-entry ?\{ "(}  " st)
    (modify-syntax-entry ?\} "){  " st)
    (modify-syntax-entry ?\[ "(]  " st)
    (modify-syntax-entry ?\] ")[  " st)
    ;; All non-word multibyte characters should be `symbol'.
    (map-char-table
     (if (featurep 'xemacs)
         (lambda (key _val)
           (and (characterp key)
                (>= (char-int key) 256)
                (/= (char-syntax key) ?w)
                (modify-syntax-entry key "_   " st)))
       (lambda (key _val)
         (and (if (consp key)
                  (and (>= (car key) 128)
                       (/= (char-syntax (car key)) ?w))
                (and (>= key 256)
                     (/= (char-syntax key) ?w)))
              (modify-syntax-entry key "_   " st))))
     (standard-syntax-table))
    st))

;;; User Functions:

(defun eshell-kill-buffer-function ()
  "Function added to `kill-buffer-hook' in Eshell buffers.
This runs the function `eshell-kill-processes-on-exit',
and the hook `eshell-exit-hook'."
  ;; It's fine to run this unconditionally since it can be customized
  ;; via the `eshell-kill-processes-on-exit' variable.
  (and (fboundp 'eshell-query-kill-processes)
       (not (memq 'eshell-query-kill-processes eshell-exit-hook))
       (eshell-query-kill-processes))
  (run-hooks 'eshell-exit-hook))

;;;###autoload
(define-derived-mode eshell-mode fundamental-mode "EShell"
  "Emacs shell interactive mode."
  (setq-local eshell-mode t)

  ;; FIXME: What the hell!?
  (setq-local eshell-mode-map (make-sparse-keymap))
  (use-local-map eshell-mode-map)

  (when eshell-status-in-mode-line
    (make-local-variable 'eshell-command-running-string)
    (let ((fmt (copy-sequence mode-line-format)))
      (setq-local mode-line-format fmt))
    (let ((mode-line-elt (memq 'mode-line-modified mode-line-format)))
      (if mode-line-elt
          (setcar mode-line-elt 'eshell-command-running-string))))

  (define-key eshell-mode-map "\r" 'eshell-send-input)
  (define-key eshell-mode-map "\M-\r" 'eshell-queue-input)
  (define-key eshell-mode-map [(meta control ?l)] 'eshell-show-output)
  (define-key eshell-mode-map [(control ?a)] 'eshell-bol)

  (setq-local eshell-command-prefix (make-symbol "eshell-command-prefix"))
  (fset eshell-command-prefix (make-sparse-keymap))
  (setq-local eshell-command-map (symbol-function eshell-command-prefix))
  (define-key eshell-mode-map [(control ?c)] eshell-command-prefix)

  ;; without this, find-tag complains about read-only text being
  ;; modified
  (if (eq (key-binding [(meta ?.)]) 'find-tag)
      (define-key eshell-mode-map [(meta ?.)] 'eshell-find-tag))
  (define-key eshell-command-map [(meta ?o)] 'eshell-mark-output)
  (define-key eshell-command-map [(meta ?d)] 'eshell-toggle-direct-send)

  (define-key eshell-command-map [(control ?a)] 'eshell-bol)
  (define-key eshell-command-map [(control ?b)] 'eshell-backward-argument)
  (define-key eshell-command-map [(control ?e)] 'eshell-show-maximum-output)
  (define-key eshell-command-map [(control ?f)] 'eshell-forward-argument)
  (define-key eshell-command-map [return]       'eshell-copy-old-input)
  (define-key eshell-command-map [(control ?m)] 'eshell-copy-old-input)
  (define-key eshell-command-map [(control ?o)] 'eshell-kill-output)
  (define-key eshell-command-map [(control ?r)] 'eshell-show-output)
  (define-key eshell-command-map [(control ?t)] 'eshell-truncate-buffer)
  (define-key eshell-command-map [(control ?u)] 'eshell-kill-input)
  (define-key eshell-command-map [(control ?w)] 'backward-kill-word)
  (define-key eshell-command-map [(control ?y)] 'eshell-repeat-argument)

  (setq local-abbrev-table eshell-mode-abbrev-table)

  (set (make-local-variable 'dired-directory) default-directory)
  (set (make-local-variable 'list-buffers-directory)
       (expand-file-name default-directory))

  ;; always set the tab width to 8 in Eshell buffers, since external
  ;; commands which do their own formatting almost always expect this
  (set (make-local-variable 'tab-width) 8)

  ;; don't ever use auto-fill in Eshell buffers
  (setq auto-fill-function nil)

  ;; always display everything from a return value
  (if (boundp 'print-length)
      (set (make-local-variable 'print-length) nil))
  (if (boundp 'print-level)
      (set (make-local-variable 'print-level) nil))

  ;; set require-final-newline to nil; otherwise, all redirected
  ;; output will end with a newline, whether or not the source
  ;; indicated it!
  (set (make-local-variable 'require-final-newline) nil)

  (set (make-local-variable 'max-lisp-eval-depth)
       (max 3000 max-lisp-eval-depth))
  (set (make-local-variable 'max-specpdl-size)
       (max 6000 max-lisp-eval-depth))

  (set (make-local-variable 'eshell-last-input-start) (point-marker))
  (set (make-local-variable 'eshell-last-input-end) (point-marker))
  (set (make-local-variable 'eshell-last-output-start) (point-marker))
  (set (make-local-variable 'eshell-last-output-end) (point-marker))
  (set (make-local-variable 'eshell-last-output-block-begin) (point))

  (let ((modules-list (copy-sequence eshell-modules-list)))
    (make-local-variable 'eshell-modules-list)
    (setq eshell-modules-list modules-list))

  ;; load extension modules into memory.  This will cause any global
  ;; variables they define to be visible, since some of the core
  ;; modules sometimes take advantage of their functionality if used.
  (dolist (module eshell-modules-list)
    (let ((module-fullname (symbol-name module))
          module-shortname)
      (if (string-match "^eshell-\\(.*\\)" module-fullname)
          (setq module-shortname
                (concat "em-" (match-string 1 module-fullname))))
      (unless module-shortname
        (error "Invalid Eshell module name: %s" module-fullname))
      (unless (featurep (intern module-shortname))
        (load module-shortname))))

  (unless (file-exists-p eshell-directory-name)
    (eshell-make-private-directory eshell-directory-name t))

  ;; Load core Eshell modules, then extension modules, for this session.
  (dolist (module (append (eshell-subgroups 'eshell) eshell-modules-list))
    (let ((load-hook (intern-soft (format "%s-load-hook" module)))
          (initfunc (intern-soft (format "%s-initialize" module))))
      (when (and load-hook (boundp load-hook))
        (if (memq initfunc (symbol-value load-hook)) (setq initfunc nil))
        (run-hooks load-hook))
      ;; So we don't need the -initialize functions on the hooks (b#5375).
      (and initfunc (fboundp initfunc) (funcall initfunc))))

  (if eshell-send-direct-to-subprocesses
      (add-hook 'pre-command-hook 'eshell-intercept-commands t t))

  (if eshell-scroll-to-bottom-on-input
      (add-hook 'pre-command-hook 'eshell-preinput-scroll-to-bottom t t))

  (when eshell-scroll-show-maximum-output
    (set (make-local-variable 'scroll-conservatively) 1000))

  (when eshell-status-in-mode-line
    (add-hook 'eshell-pre-command-hook 'eshell-command-started nil t)
    (add-hook 'eshell-post-command-hook 'eshell-command-finished nil t))

  (add-hook 'kill-buffer-hook 'eshell-kill-buffer-function t t)

  (if eshell-first-time-p
      (run-hooks 'eshell-first-time-mode-hook))
  (run-hooks 'eshell-post-command-hook))

(put 'eshell-mode 'mode-class 'special)

(defun eshell-command-started ()
  "Indicate in the mode line that a command has started."
  (setq eshell-command-running-string "**")
  (force-mode-line-update))

(defun eshell-command-finished ()
  "Indicate in the mode line that a command has finished."
  (setq eshell-command-running-string "--")
  (force-mode-line-update))

;;; Internal Functions:

(defun eshell-toggle-direct-send ()
  (interactive)
  (if eshell-send-direct-to-subprocesses
      (progn
        (setq eshell-send-direct-to-subprocesses nil)
        (remove-hook 'pre-command-hook 'eshell-intercept-commands t)
        (message "Sending subprocess input on RET"))
    (setq eshell-send-direct-to-subprocesses t)
    (add-hook 'pre-command-hook 'eshell-intercept-commands t t)
    (message "Sending subprocess input directly")))

(defun eshell-self-insert-command ()
  (interactive)
  (process-send-string
   (eshell-interactive-process)
   (char-to-string (if (symbolp last-command-event)
                       (get last-command-event 'ascii-character)
                     last-command-event))))

(defun eshell-intercept-commands ()
  (when (and (eshell-interactive-process)
             (not (and (integerp last-input-event)
                       (memq last-input-event '(?\C-x ?\C-c)))))
    (let ((possible-events (where-is-internal this-command))
          (name (symbol-name this-command))
          (intercept t))
      ;; Assume that any multikey combination which does NOT target an
      ;; Eshell command, is a combo the user wants invoked rather than
      ;; sent to the underlying subprocess.
      (unless (and (> (length name) 7)
                   (equal (substring name 0 7) "eshell-"))
        (while possible-events
          (if (> (length (car possible-events)) 1)
              (setq intercept nil possible-events nil)
            (setq possible-events (cdr possible-events)))))
      (if intercept
          (setq this-command 'eshell-self-insert-command)))))

(declare-function find-tag-interactive "etags" (prompt &optional no-default))

(defun eshell-find-tag (&optional tagname next-p regexp-p)
  "A special version of `find-tag' that ignores whether the text is read-only."
  (interactive)
  (require 'etags)
  (let ((inhibit-read-only t)
        (no-default (eobp))
        (find-tag-default-function 'ignore))
    (setq tagname (car (find-tag-interactive "Find tag: " no-default)))
    (find-tag tagname next-p regexp-p)))

(defun eshell-move-argument (limit func property arg)
  "Move forward ARG arguments."
  (catch 'eshell-incomplete
    (eshell-parse-arguments (save-excursion (eshell-bol) (point))
                            (line-end-position)))
  (let ((pos (save-excursion
               (funcall func 1)
               (while (and (> arg 0) (/= (point) limit))
                 (if (get-text-property (point) property)
                     (setq arg (1- arg)))
                 (if (> arg 0)
                     (funcall func 1)))
               (point))))
    (goto-char pos)
    (if (and (eq func 'forward-char)
             (= (1+ pos) limit))
        (forward-char 1))))

(defun eshell-forward-argument (&optional arg)
  "Move forward ARG arguments."
  (interactive "p")
  (eshell-move-argument (point-max) 'forward-char 'arg-end arg))

(defun eshell-backward-argument (&optional arg)
  "Move backward ARG arguments."
  (interactive "p")
  (eshell-move-argument (point-min) 'backward-char 'arg-begin arg))

(defun eshell-repeat-argument (&optional arg)
  (interactive "p")
  (let ((begin (save-excursion
                 (eshell-backward-argument arg)
                 (point))))
    (kill-ring-save begin (point))
    (yank)))

(defun eshell-bol ()
  "Goes to the beginning of line, then skips past the prompt, if any."
  (interactive)
  (beginning-of-line)
  (and eshell-skip-prompt-function
       (funcall eshell-skip-prompt-function)))

(defsubst eshell-push-command-mark ()
  "Push a mark at the end of the last input text."
  (push-mark (1- eshell-last-input-end) t))

(custom-add-option 'eshell-pre-command-hook 'eshell-push-command-mark)

(defsubst eshell-goto-input-start ()
  "Goto the start of the last command input.
Putting this function on `eshell-pre-command-hook' will mimic Plan 9's
9term behavior."
  (goto-char eshell-last-input-start))

(custom-add-option 'eshell-pre-command-hook 'eshell-push-command-mark)

(defsubst eshell-interactive-print (string)
  "Print STRING to the eshell display buffer."
  (eshell-output-filter nil string))

(defsubst eshell-begin-on-new-line ()
  "This function outputs a newline if not at beginning of line."
  (save-excursion
    (goto-char eshell-last-output-end)
    (or (bolp)
        (eshell-interactive-print "\n"))))

(defsubst eshell-reset (&optional no-hooks)
  "Output a prompt on a new line, aborting any current input.
If NO-HOOKS is non-nil, then `eshell-post-command-hook' won't be run."
  (goto-char (point-max))
  (setq eshell-last-input-start (point-marker)
        eshell-last-input-end (point-marker)
        eshell-last-output-start (point-marker)
        eshell-last-output-block-begin (point)
        eshell-last-output-end (point-marker))
  (eshell-begin-on-new-line)
  (unless no-hooks
    (run-hooks 'eshell-post-command-hook)
    (goto-char (point-max))))

(defun eshell-parse-command-input (beg end &optional args)
  "Parse the command input from BEG to END.
The difference is that `eshell-parse-command' expects a complete
command string (and will error if it doesn't get one), whereas this
function will inform the caller whether more input is required.

If nil is returned, more input is necessary (probably because a
multi-line input string wasn't terminated properly).  Otherwise, it
will return the parsed command."
  (let (delim command)
    (if (setq delim
              (catch 'eshell-incomplete
                (ignore
                 (setq command (eshell-parse-command (cons beg end)
                                                     args t)))))
        (ignore
         (message "Expecting completion of delimiter %c ..."
                  (if (listp delim)
                      (car delim)
                    delim)))
      command)))

(defun eshell-update-markers (pmark)
  "Update the input and output markers relative to point and PMARK."
  (set-marker eshell-last-input-start pmark)
  (set-marker eshell-last-input-end (point))
  (set-marker eshell-last-output-end (point)))

(defun eshell-queue-input (&optional use-region)
  "Queue the current input text for execution by Eshell.
Particularly, don't send the text to the current process, even if it's
waiting for input."
  (interactive "P")
  (eshell-send-input use-region t))

(defun eshell-send-input (&optional use-region queue-p no-newline)
  "Send the input received to Eshell for parsing and processing.
After `eshell-last-output-end', sends all text from that marker to
point as input.  Before that marker, calls `eshell-get-old-input' to
retrieve old input, copies it to the end of the buffer, and sends it.

If USE-REGION is non-nil, the current region (between point and mark)
will be used as input.

If QUEUE-P is non-nil, input will be queued until the next prompt,
rather than sent to the currently active process.  If no process, the
input is processed immediately.

If NO-NEWLINE is non-nil, the input is sent without an implied final
newline."
  (interactive "P")
  ;; Note that the input string does not include its terminal newline.
  (let ((proc-running-p (and (eshell-interactive-process)
                             (not queue-p)))
        (inhibit-point-motion-hooks t)
        after-change-functions)
    (unless (and proc-running-p
                 (not (eq (process-status
                           (eshell-interactive-process)) 'run)))
      (if (or proc-running-p
              (>= (point) eshell-last-output-end))
          (goto-char (point-max))
        (let ((copy (eshell-get-old-input use-region)))
          (goto-char eshell-last-output-end)
          (insert-and-inherit copy)))
      (unless (or no-newline
                  (and eshell-send-direct-to-subprocesses
                       proc-running-p))
        (insert-before-markers-and-inherit ?\n))
      (if proc-running-p
          (progn
            (eshell-update-markers eshell-last-output-end)
            (if (or eshell-send-direct-to-subprocesses
                    (= eshell-last-input-start eshell-last-input-end))
                (unless no-newline
                  (process-send-string (eshell-interactive-process) "\n"))
              (process-send-region (eshell-interactive-process)
                                   eshell-last-input-start
                                   eshell-last-input-end)))
        (if (= eshell-last-output-end (point))
            (run-hooks 'eshell-post-command-hook)
          (let (input)
            (eshell-condition-case err
                (progn
                  (setq input (buffer-substring-no-properties
                               eshell-last-output-end (1- (point))))
                  (run-hook-with-args 'eshell-expand-input-functions
                                      eshell-last-output-end (1- (point)))
                  (let ((cmd (eshell-parse-command-input
                              eshell-last-output-end (1- (point)))))
                    (when cmd
                      (eshell-update-markers eshell-last-output-end)
                      (setq input (buffer-substring-no-properties
                                   eshell-last-input-start
                                   (1- eshell-last-input-end)))
                      (run-hooks 'eshell-input-filter-functions)
                      (and (catch 'eshell-terminal
                             (ignore
                              (if (eshell-invoke-directly cmd)
                                  (eval cmd)
                                (eshell-eval-command cmd input))))
                           (eshell-life-is-too-much)))))
              (quit
               (eshell-reset t)
               (run-hooks 'eshell-post-command-hook)
               (signal 'quit nil))
              (error
               (eshell-reset t)
               (eshell-interactive-print
                (concat (error-message-string err) "\n"))
               (run-hooks 'eshell-post-command-hook)
               (insert-and-inherit input)))))))))

(defsubst eshell-kill-new ()
  "Add the last input text to the kill ring."
  (kill-ring-save eshell-last-input-start eshell-last-input-end))

(custom-add-option 'eshell-input-filter-functions 'eshell-kill-new)

(defun eshell-output-filter (process string)
  "Send the output from PROCESS (STRING) to the interactive display.
This is done after all necessary filtering has been done."
  (let ((oprocbuf (if process (process-buffer process)
                    (current-buffer)))
        (inhibit-point-motion-hooks t)
        after-change-functions)
    (let ((functions eshell-preoutput-filter-functions))
      (while (and functions string)
        (setq string (funcall (car functions) string))
        (setq functions (cdr functions))))
    (if (and string oprocbuf (buffer-name oprocbuf))
        (let (opoint obeg oend)
          (with-current-buffer oprocbuf
            (setq opoint (point))
            (setq obeg (point-min))
            (setq oend (point-max))
            (let ((buffer-read-only nil)
                  (nchars (length string))
                  (ostart nil))
              (widen)
              (goto-char eshell-last-output-end)
              (setq ostart (point))
              (if (<= (point) opoint)
                  (setq opoint (+ opoint nchars)))
              (if (< (point) obeg)
                  (setq obeg (+ obeg nchars)))
              (if (<= (point) oend)
                  (setq oend (+ oend nchars)))
              (insert-before-markers string)
              (if (= (window-start) (point))
                  (set-window-start (selected-window)
                                    (- (point) nchars)))
              (if (= (point) eshell-last-input-end)
                  (set-marker eshell-last-input-end
                              (- eshell-last-input-end nchars)))
              (set-marker eshell-last-output-start ostart)
              (set-marker eshell-last-output-end (point))
              (force-mode-line-update))
            (narrow-to-region obeg oend)
            (goto-char opoint)
            (eshell-run-output-filters))))))

(defun eshell-run-output-filters ()
  "Run the `eshell-output-filter-functions' on the current output."
  (save-current-buffer
    (run-hooks 'eshell-output-filter-functions))
  (setq eshell-last-output-block-begin
        (marker-position eshell-last-output-end)))

;;; jww (1999-10-23): this needs testing
(defun eshell-preinput-scroll-to-bottom ()
  "Go to the end of buffer in all windows showing it.
Movement occurs if point in the selected window is not after the
process mark, and `this-command' is an insertion command.  Insertion
commands recognized are `self-insert-command', `yank', and
`hilit-yank'.  Depends on the value of
`eshell-scroll-to-bottom-on-input'.

This function should be a pre-command hook."
  (if (memq this-command '(self-insert-command yank hilit-yank))
      (let* ((selected (selected-window))
             (current (current-buffer))
             (scroll eshell-scroll-to-bottom-on-input))
        (if (< (point) eshell-last-output-end)
            (if (eq scroll 'this)
                (goto-char (point-max))
              (walk-windows
               (function
                (lambda (window)
                  (when (and (eq (window-buffer window) current)
                             (or (eq scroll t) (eq scroll 'all)))
                    (select-window window)
                    (goto-char (point-max))
                    (select-window selected))))
               nil t))))))

;;; jww (1999-10-23): this needs testing
(defun eshell-postoutput-scroll-to-bottom ()
  "Go to the end of buffer in all windows showing it.
Does not scroll if the current line is the last line in the buffer.
Depends on the value of `eshell-scroll-to-bottom-on-output' and
`eshell-scroll-show-maximum-output'.

This function should be in the list `eshell-output-filter-functions'."
  (let* ((selected (selected-window))
         (current (current-buffer))
         (scroll eshell-scroll-to-bottom-on-output))
    (unwind-protect
        (walk-windows
         (function
          (lambda (window)
            (if (eq (window-buffer window) current)
                (progn
                  (select-window window)
                  (if (and (< (point) eshell-last-output-end)
                           (or (eq scroll t) (eq scroll 'all)
                               ;; Maybe user wants point to jump to end.
                               (and (eq scroll 'this)
                                    (eq selected window))
                               (and (eq scroll 'others)
                                    (not (eq selected window)))
                               ;; If point was at the end, keep it at end.
                               (>= (point) eshell-last-output-start)))
                      (goto-char eshell-last-output-end))
                  ;; Optionally scroll so that the text
                  ;; ends at the bottom of the window.
                  (if (and eshell-scroll-show-maximum-output
                           (>= (point) eshell-last-output-end))
                      (save-excursion
                        (goto-char (point-max))
                        (recenter -1)))
                  (select-window selected)))))
         nil t)
      (set-buffer current))))

(defun eshell-beginning-of-input ()
  "Return the location of the start of the previous input."
  eshell-last-input-start)

(defun eshell-beginning-of-output ()
  "Return the location of the end of the previous output block."
  eshell-last-input-end)

(defun eshell-end-of-output ()
  "Return the location of the end of the previous output block."
  (if (eshell-using-module 'eshell-prompt)
      eshell-last-output-start
    eshell-last-output-end))

(defun eshell-kill-output ()
  "Kill all output from interpreter since last input.
Does not delete the prompt."
  (interactive)
  (save-excursion
    (goto-char (eshell-beginning-of-output))
    (insert "*** output flushed ***\n")
    (delete-region (point) (eshell-end-of-output))))

(defun eshell-show-output (&optional arg)
  "Display start of this batch of interpreter output at top of window.
Sets mark to the value of point when this command is run.
With a prefix argument, narrows region to last command output."
  (interactive "P")
  (goto-char (eshell-beginning-of-output))
  (set-window-start (selected-window)
                    (save-excursion
                      (goto-char (eshell-beginning-of-input))
                      (line-beginning-position)))
  (if arg
      (narrow-to-region (eshell-beginning-of-output)
                        (eshell-end-of-output)))
  (eshell-end-of-output))

(defun eshell-mark-output (&optional arg)
  "Display start of this batch of interpreter output at top of window.
Sets mark to the value of point when this command is run.
With a prefix argument, narrows region to last command output."
  (interactive "P")
  (push-mark (eshell-show-output arg)))

(defun eshell-kill-input ()
  "Kill all text from last stuff output by interpreter to point."
  (interactive)
  (if (> (point) eshell-last-output-end)
      (kill-region eshell-last-output-end (point))
    (let ((here (point)))
      (eshell-bol)
      (kill-region (point) here))))

(defun eshell-show-maximum-output (&optional interactive)
  "Put the end of the buffer at the bottom of the window.
When run interactively, widen the buffer first."
  (interactive "p")
  (if interactive
      (widen))
  (goto-char (point-max))
  (recenter -1))

(defun eshell-get-old-input (&optional use-current-region)
  "Return the command input on the current line."
  (if use-current-region
      (buffer-substring (min (point) (mark))
                        (max (point) (mark)))
    (save-excursion
      (beginning-of-line)
      (and eshell-skip-prompt-function
           (funcall eshell-skip-prompt-function))
      (let ((beg (point)))
        (end-of-line)
        (buffer-substring beg (point))))))

(defun eshell-copy-old-input ()
  "Insert after prompt old input at point as new input to be edited."
  (interactive)
  (let ((input (eshell-get-old-input)))
    (goto-char eshell-last-output-end)
    (insert-and-inherit input)))

(defun eshell/exit ()
  "Leave or kill the Eshell buffer, depending on `eshell-kill-on-exit'."
  (throw 'eshell-terminal t))

(defun eshell-life-is-too-much ()
  "Kill the current buffer (or bury it).  Good-bye Eshell."
  (interactive)
  (if (not eshell-kill-on-exit)
      (bury-buffer)
    (kill-buffer (current-buffer))))

(defun eshell-truncate-buffer ()
  "Truncate the buffer to `eshell-buffer-maximum-lines'.
This function could be on `eshell-output-filter-functions' or bound to
a key."
  (interactive)
  (save-excursion
    (goto-char eshell-last-output-end)
    (let ((lines (count-lines 1 (point)))
          (inhibit-read-only t))
      (forward-line (- eshell-buffer-maximum-lines))
      (beginning-of-line)
      (let ((pos (point)))
        (if (bobp)
            (if (called-interactively-p 'interactive)
                (message "Buffer too short to truncate"))
          (delete-region (point-min) (point))
          (if (called-interactively-p 'interactive)
              (message "Truncated buffer from %d to %d lines (%.1fk freed)"
                       lines eshell-buffer-maximum-lines
                       (/ pos 1024.0))))))))

(custom-add-option 'eshell-output-filter-functions
                   'eshell-truncate-buffer)

(defun eshell-send-invisible ()
  "Read a string without echoing.
Then send it to the process running in the current buffer."
  (interactive) ; Don't pass str as argument, to avoid snooping via C-x ESC ESC
  (let ((str (read-passwd
              (format "%s Password: "
                      (process-name (eshell-interactive-process))))))
    (if (stringp str)
        (process-send-string (eshell-interactive-process)
                             (concat str "\n"))
      (message "Warning: text will be echoed"))))

(defun eshell-watch-for-password-prompt ()
  "Prompt in the minibuffer for password and send without echoing.
This function uses `eshell-send-invisible' to read and send a password to the
buffer's process if STRING contains a password prompt defined by
`eshell-password-prompt-regexp'.

This function could be in the list `eshell-output-filter-functions'."
  (when (eshell-interactive-process)
    (save-excursion
      (let ((case-fold-search t))
        (goto-char eshell-last-output-block-begin)
        (beginning-of-line)
        (if (re-search-forward eshell-password-prompt-regexp
                               eshell-last-output-end t)
            (eshell-send-invisible))))))

(custom-add-option 'eshell-output-filter-functions
                   'eshell-watch-for-password-prompt)

(defun eshell-handle-control-codes ()
  "Act properly when certain control codes are seen."
  (save-excursion
    (goto-char eshell-last-output-block-begin)
    (unless (eolp)
      (beginning-of-line))
    (while (< (point) eshell-last-output-end)
      (let ((char (char-after)))
        (cond
         ((eq char ?\r)
          (if (< (1+ (point)) eshell-last-output-end)
              (if (memq (char-after (1+ (point)))
                        '(?\n ?\r))
                  (delete-char 1)
                (let ((end (1+ (point))))
                  (beginning-of-line)
                  (delete-region (point) end)))
            (add-text-properties (point) (1+ (point))
                                 '(invisible t))
            (forward-char)))
         ((eq char ?\a)
          (delete-char 1)
          (beep))
         ((eq char ?\C-h)
          (delete-region (1- (point)) (1+ (point))))
         (t
          (forward-char)))))))

(custom-add-option 'eshell-output-filter-functions
                   'eshell-handle-control-codes)

(autoload 'ansi-color-apply-on-region "ansi-color")

(defun eshell-handle-ansi-color ()
  "Handle ANSI color codes."
  (ansi-color-apply-on-region eshell-last-output-start
                              eshell-last-output-end))

(custom-add-option 'eshell-output-filter-functions
                   'eshell-handle-ansi-color)

;;; esh-mode.el ends here

(provide 'esh-opt)

(require 'esh-ext)

;; Unused.
;; (defgroup eshell-opt nil
;;   "The options processing code handles command argument parsing for
;; Eshell commands implemented in Lisp."
;;   :tag "Command options processing"
;;   :group 'eshell)

;;; User Functions:

(defmacro eshell-eval-using-options (name macro-args options &rest body-forms)
  "Process NAME's MACRO-ARGS using a set of command line OPTIONS.
After doing so, stores settings in local symbols as declared by OPTIONS;
then evaluates BODY-FORMS -- assuming all was OK.

OPTIONS is a list, beginning with one or more elements of the form:
\(SHORT LONG VALUE SYMBOL HELP-STRING)
Each of these elements represents a particular command-line switch.

SHORT is either nil, or a character that can be used as a switch -SHORT.
LONG is either nil, or a string that can be used as a switch --LONG.
At least one of SHORT and LONG must be non-nil.
VALUE is the value associated with the option.  It can be either:
  t   - the option needs a value to be specified after the switch;
  nil - the option is given the value t;
  anything else - specifies the actual value for the option.
SYMBOL is either nil, or the name of the Lisp symbol that will be bound
to VALUE.  A nil SYMBOL calls `eshell-show-usage', and so is appropriate
for a \"--help\" type option.
HELP-STRING is a documentation string for the option.

Any remaining elements of OPTIONS are :KEYWORD arguments.  Some take
arguments, some do not.  The recognized :KEYWORDS are:

:external STRING
  STRING is an external command to run if there are unknown switches.

:usage STRING
  STRING is the initial part of the command's documentation string.
  It appears before the options are listed.

:post-usage STRING
  STRING is an optional trailing part of the command's documentation string.
  It appears after the options, but before the final part of the
  documentation about the associated external command (if there is one).

:show-usage
  If present, then show the usage message if the command is called with no
  arguments.

:preserve-args
  If present, do not pass MACRO-ARGS through `eshell-flatten-list'
and `eshell-stringify-list'.

For example, OPTIONS might look like:

  '((?C  nil         nil multi-column    \"multi-column display\")
    (nil \"help\"      nil nil             \"show this usage display\")
    (?r  \"reverse\"   nil reverse-list    \"reverse order while sorting\")
    :external \"ls\"
    :usage \"[OPTION]... [FILE]...
  List information about the FILEs (the current directory by default).
  Sort entries alphabetically across.\")

`eshell-eval-using-options' returns the value of the last form in
BODY-FORMS.  If instead an external command is run (because of
an unknown option), the tag `eshell-external' will be thrown with
the new process for its value.

Lastly, any remaining arguments will be available in a locally
interned variable `args' (created using a `let' form)."
  (declare (debug (form form sexp body)))
  `(let* ((temp-args
           ,(if (memq ':preserve-args (cadr options))
                macro-args
              (list 'eshell-stringify-list
                    (list 'eshell-flatten-list macro-args))))
          (processed-args (eshell--do-opts ,name ,options temp-args))
          ,@(delete-dups
             (delq nil (mapcar (lambda (opt)
                                 (and (listp opt) (nth 3 opt)
                                      `(,(nth 3 opt) (pop processed-args))))
                               ;; `options' is of the form (quote OPTS).
                               (cadr options))))
          (args processed-args))
     ,@body-forms))

;;; Internal Functions:

;; Documented part of the interface; see eshell-eval-using-options.
(defvar eshell--args)

(defun eshell--do-opts (name options args)
  "Helper function for `eshell-eval-using-options'.
This code doesn't really need to be macro expanded everywhere."
  (let ((ext-command
         (catch 'eshell-ext-command
           (let ((usage-msg
                  (catch 'eshell-usage
                    (if (and (= (length args) 0)
                             (memq ':show-usage options))
                        (eshell-show-usage name options)
                      (setq args (eshell--process-args name args options))
                      nil))))
             (when usage-msg
               (error "%s" usage-msg))))))
    (if ext-command
        (throw 'eshell-external
               (eshell-external-command ext-command args))
      args)))

(defun eshell-show-usage (name options)
  "Display the usage message for NAME, using OPTIONS."
  (let ((usage (format "usage: %s %s\n\n" name
                       (cadr (memq ':usage options))))
        (extcmd (memq ':external options))
        (post-usage (memq ':post-usage options))
        had-option)
    (while options
      (when (listp (car options))
        (let ((opt (car options)))
          (setq had-option t)
          (cond ((and (nth 0 opt)
                      (nth 1 opt))
                 (setq usage
                       (concat usage
                               (format "    %-20s %s\n"
                                       (format "-%c, --%s" (nth 0 opt)
                                               (nth 1 opt))
                                       (nth 4 opt)))))
                ((nth 0 opt)
                 (setq usage
                       (concat usage
                               (format "    %-20s %s\n"
                                       (format "-%c" (nth 0 opt))
                                       (nth 4 opt)))))
                ((nth 1 opt)
                 (setq usage
                       (concat usage
                               (format "    %-20s %s\n"
                                       (format "    --%s" (nth 1 opt))
                                       (nth 4 opt)))))
                (t (setq had-option nil)))))
      (setq options (cdr options)))
    (if post-usage
        (setq usage (concat usage (and had-option "\n")
                            (cadr post-usage))))
    (when extcmd
      (setq extcmd (eshell-search-path (cadr extcmd)))
      (if extcmd
          (setq usage
                (concat usage
                        (format "
This command is implemented in Lisp.  If an unrecognized option is
passed to this command, the external version '%s'
will be called instead." extcmd)))))
    (throw 'eshell-usage usage)))

(defun eshell--set-option (name ai opt options opt-vals)
  "Using NAME's remaining args (index AI), set the OPT within OPTIONS.
If the option consumes an argument for its value, the argument list
will be modified."
  (if (not (nth 3 opt))
      (eshell-show-usage name options)
    (setcdr (assq (nth 3 opt) opt-vals)
            (if (eq (nth 2 opt) t)
                (if (> ai (length eshell--args))
                    (error "%s: missing option argument" name)
                  (prog1 (nth ai eshell--args)
                    (if (> ai 0)
                        (setcdr (nthcdr (1- ai) eshell--args)
                                (nthcdr (1+ ai) eshell--args))
                      (setq eshell--args (cdr eshell--args)))))
              (or (nth 2 opt) t)))))

(defun eshell--process-option (name switch kind ai options opt-vals)
  "For NAME, process SWITCH (of type KIND), from args at index AI.
The SWITCH will be looked up in the set of OPTIONS.

SWITCH should be either a string or character.  KIND should be the
integer 0 if it's a character, or 1 if it's a string.

The SWITCH is then be matched against OPTIONS.  If no matching handler
is found, and an :external command is defined (and available), it will
be called; otherwise, an error will be triggered to say that the
switch is unrecognized."
  (let* ((opts options)
         found)
    (while opts
      (if (and (listp (car opts))
               (nth kind (car opts))
               (equal switch (nth kind (car opts))))
          (progn
            (eshell--set-option name ai (car opts) options opt-vals)
            (setq found t opts nil))
        (setq opts (cdr opts))))
    (unless found
      (let ((extcmd (memq ':external options)))
        (when extcmd
          (setq extcmd (eshell-search-path (cadr extcmd)))
          (if extcmd
              (throw 'eshell-ext-command extcmd)
            (error (if (characterp switch) "%s: unrecognized option -%c"
                     "%s: unrecognized option --%s")
                   name switch)))))))

(defun eshell--process-args (name args options)
  "Process the given ARGS using OPTIONS."
  (let* ((seen ())
         (opt-vals (delq nil (mapcar (lambda (opt)
                                       (when (listp opt)
                                         (let ((sym (nth 3 opt)))
                                           (when (and sym (not (memq sym seen)))
                                             (push sym seen)
                                             (list sym)))))
                                     options)))
         (ai 0) arg
         (eshell--args args))
    (while (< ai (length args))
      (setq arg (nth ai args))
      (if (not (and (stringp arg)
                    (string-match "^-\\(-\\)?\\(.*\\)" arg)))
          (setq ai (1+ ai))
        (let* ((dash (match-string 1 arg))
               (switch (match-string 2 arg)))
          (if (= ai 0)
              (setq args (cdr args))
            (setcdr (nthcdr (1- ai) args) (nthcdr (1+ ai) args)))
          (if dash
              (if (> (length switch) 0)
                  (eshell--process-option name switch 1 ai options opt-vals)
                (setq ai (length args)))
            (let ((len (length switch))
                  (index 0))
              (while (< index len)
                (eshell--process-option name (aref switch index)
                                        0 ai options opt-vals)
                (setq index (1+ index))))))))
    (nconc (mapcar #'cdr opt-vals) args)))

;;;### (autoloads nil "em-alias" "em-alias.el" "707c31f56d49cb078afc75e55a97e0af")
;;; Generated autoloads from em-alias.el

(defgroup eshell-alias nil "\
Command aliases allow for easy definition of alternate commands." :tag "Command aliases" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-banner" "em-banner.el" "41977a9bafecac8de00e79bb48a69752")
;;; Generated autoloads from em-banner.el

(defgroup eshell-banner nil "\
This sample module displays a welcome banner at login.
It exists so that others wishing to create their own Eshell extension
modules may have a simple template to begin with." :tag "Login banner" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-basic" "em-basic.el" "734b6b65d5fb1bc0b4404b9e5c9500bb")
;;; Generated autoloads from em-basic.el

(defgroup eshell-basic nil "\
The \"basic\" code provides a set of convenience functions which
are traditionally considered shell builtins.  Since all of the
functionality provided by them is accessible through Lisp, they are
not really builtins at all, but offer a command-oriented way to do the
same thing." :tag "Basic shell commands" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-cmpl" "em-cmpl.el" "e0644cd631973db6bcee04e39953f2e9")
;;; Generated autoloads from em-cmpl.el

(defgroup eshell-cmpl nil "\
This module provides a programmable completion function bound to
the TAB key, which allows for completing command names, file names,
variable names, arguments, etc." :tag "Argument completion" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-dirs" "em-dirs.el" "8d1ce0559b4dcafb48d0dfd5f5ee4c5e")
;;; Generated autoloads from em-dirs.el

(defgroup eshell-dirs nil "\
Directory navigation involves changing directories, examining the
current directory, maintaining a directory stack, and also keeping
track of a history of the last directory locations the user was in.
Emacs does provide standard Lisp definitions of `pwd' and `cd', but
they lack somewhat in feel from the typical shell equivalents." :tag "Directory navigation" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-glob" "em-glob.el" "42b49ece984f74c6cbb511f11b7f7957")
;;; Generated autoloads from em-glob.el

(defgroup eshell-glob nil "\
This module provides extended globbing syntax, similar what is used
by zsh for filename generation." :tag "Extended filename globbing" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-hist" "em-hist.el" "0a1e51f3d1a4367889dc3b125aace948")
;;; Generated autoloads from em-hist.el

(defgroup eshell-hist nil "\
This module provides command history management." :tag "History list management" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-ls" "em-ls.el" "ed4f326637862592600f5a578702fe31")
;;; Generated autoloads from em-ls.el

(defgroup eshell-ls nil "\
This module implements the \"ls\" utility fully in Lisp.  If it is
passed any unrecognized command switches, it will revert to the
operating system's version.  This version of \"ls\" uses text
properties to colorize its output based on the setting of
`eshell-ls-use-colors'." :tag "Implementation of `ls' in Lisp" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-pred" "em-pred.el" "fb7ea1512e12443c7581da44f12c8afb")
;;; Generated autoloads from em-pred.el

(defgroup eshell-pred nil "\
This module allows for predicates to be applied to globbing
patterns (similar to zsh), in addition to string modifiers which can
be applied either to globbing results, variable references, or just
ordinary strings." :tag "Value modifiers and predicates" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-prompt" "em-prompt.el" "eb16fd1bf010a99f3eef04de70e3ed5e")
;;; Generated autoloads from em-prompt.el

(defgroup eshell-prompt nil "\
This module provides command prompts, and navigation between them,
as is common with most shells." :tag "Command prompts" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-rebind" "em-rebind.el" "9e01cd6064cfba95fc932046f73b754e")
;;; Generated autoloads from em-rebind.el

(defgroup eshell-rebind nil "\
This module allows for special keybindings that only take effect
while the point is in a region of input text.  By default, it binds
C-a to move to the beginning of the input text (rather than just the
beginning of the line), and C-p and C-n to move through the input
history, C-u kills the current input text, etc.  It also, if
`eshell-confine-point-to-input' is non-nil, does not allow certain
commands to cause the point to leave the input area, such as
`backward-word', `previous-line', etc.  This module intends to mimic
the behavior of normal shells while the user editing new input text." :tag "Rebind keys at input" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-script" "em-script.el" "1efe96557c2d63d5fd3c71749948bf09")
;;; Generated autoloads from em-script.el

(defgroup eshell-script nil "\
This module allows for the execution of files containing Eshell
commands, as a script file." :tag "Running script files." :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-smart" "em-smart.el" "630de6eac441ad0c429274813811185c")
;;; Generated autoloads from em-smart.el

(defgroup eshell-smart nil "\
This module combines the facility of normal, modern shells with
some of the edit/review concepts inherent in the design of Plan 9's
9term.  See the docs for more details.

Most likely you will have to turn this option on and play around with
it to get a real sense of how it works." :tag "Smart display of output" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-term" "em-term.el" "0324c89efe2bd007431a8359cd296845")
;;; Generated autoloads from em-term.el

(defgroup eshell-term nil "\
This module causes visual commands (e.g., 'vi') to be executed by
the `term' package, which comes with Emacs.  This package handles most
of the ANSI control codes, allowing curses-based applications to run
within an Emacs window.  The variable `eshell-visual-commands' defines
which commands are considered visual in nature." :tag "Running visual commands" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-tramp" "em-tramp.el" "0e53abcffb816dc09a18310db23f325e")
;;; Generated autoloads from em-tramp.el

(defgroup eshell-tramp nil "\
This module defines commands that use TRAMP in a way that is
  not transparent to the user.  So far, this includes only the
  built-in su and sudo commands, which are not compatible with
  the full, external su and sudo commands, and require the user
  to understand how to use the TRAMP sudo method." :tag "TRAMP Eshell features" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-unix" "em-unix.el" "caf2316c3cb6b224851a251d6e988d27")
;;; Generated autoloads from em-unix.el

(defgroup eshell-unix nil "\
This module defines many of the more common UNIX utilities as
aliases implemented in Lisp.  These include mv, ln, cp, rm, etc.  If
the user passes arguments which are too complex, or are unrecognized
by the Lisp variant, the external version will be called (if
available).  The only reason not to use them would be because they are
usually much slower.  But in several cases their tight integration
with Eshell makes them more versatile than their traditional cousins
\(such as being able to use `kill' to kill Eshell background processes
by name)." :tag "UNIX commands in Lisp" :group (quote eshell-module))

;;;***

;;;### (autoloads nil "em-xtra" "em-xtra.el" "33f46b7830cca1bcc462a17cfc923969")
;;; Generated autoloads from em-xtra.el

(defgroup eshell-xtra nil "\
This module defines some extra alias functions which are entirely
optional.  They can be viewed as samples for how to write Eshell alias
functions, or as aliases which make some of Emacs's behavior more
naturally accessible within Emacs." :tag "Extra alias functions" :group (quote eshell-module))

;;;***

(provide 'esh-groups)

(require 'eshell)

;;;###autoload
(progn
(defgroup eshell-alias nil
  "Command aliases allow for easy definition of alternate commands."
  :tag "Command aliases"
  ;; :link '(info-link "(eshell)Command aliases")
  :group 'eshell-module))

(defcustom eshell-aliases-file (expand-file-name "alias" eshell-directory-name)
  "The file in which aliases are kept.
Whenever an alias is defined by the user, using the `alias' command,
it will be written to this file.  Thus, alias definitions (and
deletions) are always permanent.  This approach was chosen for the
sake of simplicity, since that's pretty much the only benefit to be
gained by using this module."
  :type 'file
  :group 'eshell-alias)

(defcustom eshell-bad-command-tolerance 3
  "The number of failed commands to ignore before creating an alias."
  :type 'integer
  ;; :link '(custom-manual "(eshell)Auto-correction of bad commands")
  :group 'eshell-alias)

(defcustom eshell-alias-load-hook nil
  "A hook that gets run when `eshell-alias' is loaded."
  :version "24.1"                       ; removed eshell-alias-initialize
  :type 'hook
  :group 'eshell-alias)

(defvar eshell-command-aliases-list nil
  "A list of command aliases currently defined by the user.
Each element of this alias is a list of the form:

  (NAME DEFINITION)

Where NAME is the textual name of the alias, and DEFINITION is the
command string to replace that command with.

Note: this list should not be modified in your init file.
Rather, any desired alias definitions should be declared using
the `alias' command, which will automatically write them to the
file named by `eshell-aliases-file'.")

(put 'eshell-command-aliases-list 'risky-local-variable t)

(defvar eshell-failed-commands-alist nil
  "An alist of command name failures.")

(defun eshell-alias-initialize ()
  "Initialize the alias handling code."
  (make-local-variable 'eshell-failed-commands-alist)
  (add-hook 'eshell-alternate-command-hook 'eshell-fix-bad-commands t t)
  (eshell-read-aliases-list)
  (add-hook 'eshell-named-command-hook 'eshell-maybe-replace-by-alias t t)
  (make-local-variable 'eshell-complex-commands)
  (add-to-list 'eshell-complex-commands 'eshell-command-aliased-p))

(defun eshell-command-aliased-p (name)
  (assoc name eshell-command-aliases-list))

(defun eshell/alias (&optional alias &rest definition)
  "Define an ALIAS in the user's alias list using DEFINITION."
  (if (not alias)
      (dolist (alias eshell-command-aliases-list)
        (eshell-print (apply 'format "alias %s %s\n" alias)))
    (if (not definition)
        (setq eshell-command-aliases-list
              (delq (assoc alias eshell-command-aliases-list)
                    eshell-command-aliases-list))
      (and (stringp definition)
           (set-text-properties 0 (length definition) nil definition))
      (let ((def (assoc alias eshell-command-aliases-list))
            (alias-def (list alias
                             (eshell-flatten-and-stringify definition))))
        (if def
            (setq eshell-command-aliases-list
                  (delq def eshell-command-aliases-list)))
        (setq eshell-command-aliases-list
              (cons alias-def eshell-command-aliases-list))))
    (eshell-write-aliases-list))
  nil)

(defvar pcomplete-stub)
(autoload 'pcomplete-here "pcomplete")

(defun pcomplete/eshell-mode/alias ()
  "Completion function for Eshell's `alias' command."
  (pcomplete-here (eshell-alias-completions pcomplete-stub)))

(defun eshell-read-aliases-list ()
  "Read in an aliases list from `eshell-aliases-file'."
  (let ((file eshell-aliases-file))
    (when (file-readable-p file)
      (setq eshell-command-aliases-list
            (with-temp-buffer
              (let (eshell-command-aliases-list)
                (insert-file-contents file)
                (while (not (eobp))
                  (if (re-search-forward
                       "^alias\\s-+\\(\\S-+\\)\\s-+\\(.+\\)")
                      (setq eshell-command-aliases-list
                            (cons (list (match-string 1)
                                        (match-string 2))
                                  eshell-command-aliases-list)))
                  (forward-line 1))
                eshell-command-aliases-list))))))

(defun eshell-write-aliases-list ()
  "Write out the current aliases into `eshell-aliases-file'."
  (if (file-writable-p (file-name-directory eshell-aliases-file))
      (let ((eshell-current-handles
             (eshell-create-handles eshell-aliases-file 'overwrite)))
        (eshell/alias)
        (eshell-close-handles 0))))

(defsubst eshell-lookup-alias (name)
  "Check whether NAME is aliased.  Return the alias if there is one."
  (assoc name eshell-command-aliases-list))

(defvar eshell-prevent-alias-expansion nil)

(defun eshell-maybe-replace-by-alias (command args)
  "If COMMAND has an alias definition, call that instead using ARGS."
  (unless (and eshell-prevent-alias-expansion
               (member command eshell-prevent-alias-expansion))
    (let ((alias (eshell-lookup-alias command)))
      (if alias
          (throw 'eshell-replace-command
                 `(let ((eshell-command-name ',eshell-last-command-name)
                        (eshell-command-arguments ',eshell-last-arguments)
                        (eshell-prevent-alias-expansion
                         ',(cons command eshell-prevent-alias-expansion)))
                    ,(eshell-parse-command (nth 1 alias))))))))

(defun eshell-alias-completions (name)
  "Find all possible completions for NAME.
These are all the command aliases which begin with NAME."
  (let (completions)
    (dolist (alias eshell-command-aliases-list)
      (if (string-match (concat "^" name) (car alias))
          (setq completions (cons (car alias) completions))))
    completions))

(defun eshell-fix-bad-commands (name)
  "If the user repeatedly a bad command NAME, make an alias for them."
  (ignore
   (unless (file-name-directory name)
     (let ((entry (assoc name eshell-failed-commands-alist)))
       (if (not entry)
           (setq eshell-failed-commands-alist
                 (cons (cons name 1) eshell-failed-commands-alist))
         (if (< (cdr entry) eshell-bad-command-tolerance)
             (setcdr entry (1+ (cdr entry)))
           (let ((alias (concat
                         (read-string
                          (format "Define alias for \"%s\": " name))
                         " $*")))
             (eshell/alias name alias)
             (throw 'eshell-replace-command
                    (list
                     'let
                     (list
                      (list 'eshell-command-name
                            (list 'quote name))
                      (list 'eshell-command-arguments
                            (list 'quote eshell-last-arguments))
                      (list 'eshell-prevent-alias-expansion
                            (list 'quote
                                  (cons name
                                        eshell-prevent-alias-expansion))))
                     (eshell-parse-command alias))))))))))

(provide 'em-alias)

(eval-when-compile
  (require 'cl-lib))

(require 'esh-util)
(require 'esh-mode)
(require 'eshell)

;;;###autoload
(progn
(defgroup eshell-banner nil
  "This sample module displays a welcome banner at login.
It exists so that others wishing to create their own Eshell extension
modules may have a simple template to begin with."
  :tag "Login banner"
  ;; :link '(info-link "(eshell)Login banner")
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-banner-message ""
  "The banner message to be displayed when Eshell is loaded.
This can be any sexp, and should end with at least two newlines."
  :type 'sexp
  :group 'eshell-banner)

(put 'eshell-banner-message 'risky-local-variable t)

(defcustom eshell-banner-load-hook nil
  "A list of functions to run when `eshell-banner' is loaded."
  :version "24.1"                       ; removed eshell-banner-initialize
  :type 'hook
  :group 'eshell-banner)

(defun eshell-banner-initialize ()
  "Output a welcome banner on initialization."
  ;; it's important to use `eshell-interactive-print' rather than
  ;; `insert', because `insert' doesn't know how to interact with the
  ;; I/O code used by Eshell
  (unless eshell-non-interactive-p
    (cl-assert eshell-mode)
    (cl-assert eshell-banner-message)
    (let ((msg (eval eshell-banner-message)))
      (cl-assert msg)
      (eshell-interactive-print msg))))

(provide 'em-banner)

(require 'esh-util)
(require 'eshell)
(require 'esh-opt)

;;;###autoload
(progn
(defgroup eshell-basic nil
  "The \"basic\" code provides a set of convenience functions which
are traditionally considered shell builtins.  Since all of the
functionality provided by them is accessible through Lisp, they are
not really builtins at all, but offer a command-oriented way to do the
same thing."
  :tag "Basic shell commands"
  :group 'eshell-module))

(defcustom eshell-plain-echo-behavior nil
  "If non-nil, `echo' tries to behave like an ordinary shell echo.
This comes at some detriment to Lisp functionality.  However, the Lisp
equivalent of `echo' can always be achieved by using `identity'."
  :type 'boolean
  :group 'eshell-basic)

;;; Functions:

(defun eshell-echo (args &optional output-newline)
  "Implementation code for a Lisp version of `echo'.
It returns a formatted value that should be passed to `eshell-print'
or `eshell-printn' for display."
  (if eshell-plain-echo-behavior
      (concat (apply 'eshell-flatten-and-stringify args) "\n")
    (let ((value
           (cond
            ((= (length args) 0) "")
            ((= (length args) 1)
             (car args))
            (t
             (mapcar
              (function
               (lambda (arg)
                 (if (stringp arg)
                     (set-text-properties 0 (length arg) nil arg))
                 arg))
              args)))))
      (if output-newline
          (cond
           ((stringp value)
            (concat value "\n"))
           ((listp value)
            (append value (list "\n")))
           (t
            (concat (eshell-stringify value) "\n")))
        value))))

(defun eshell/echo (&rest args)
  "Implementation of `echo'.  See `eshell-plain-echo-behavior'."
  (eshell-eval-using-options
   "echo" args
   '((?n nil nil output-newline "terminate with a newline")
     (?h "help" nil nil "output this help screen")
     :preserve-args
     :usage "[-n] [object]")
   (eshell-echo args output-newline)))

(defun eshell/printnl (&rest args)
  "Print out each of the arguments, separated by newlines."
  (let ((elems (eshell-flatten-list args)))
    (while elems
      (eshell-printn (eshell-echo (list (car elems))))
      (setq elems (cdr elems)))))

(defun eshell/listify (&rest args)
  "Return the argument(s) as a single list."
  (if (> (length args) 1)
      args
    (if (listp (car args))
        (car args)
      (list (car args)))))

(defun eshell/umask (&rest args)
  "Shell-like implementation of `umask'."
  (eshell-eval-using-options
   "umask" args
   '((?S "symbolic" nil symbolic-p "display umask symbolically")
     (?h "help" nil nil  "display this usage message")
     :usage "[-S] [mode]")
   (if (or (not args) symbolic-p)
       (let ((modstr
              (concat "000"
                      (format "%o"
                              (logand (lognot (default-file-modes))
                                      511)))))
         (setq modstr (substring modstr (- (length modstr) 3)))
         (when symbolic-p
           (let ((mode (default-file-modes)))
             (setq modstr
                   (format
                    "u=%s,g=%s,o=%s"
                    (concat (and (= (logand mode 64) 64) "r")
                            (and (= (logand mode 128) 128) "w")
                            (and (= (logand mode 256) 256) "x"))
                    (concat (and (= (logand mode 8) 8) "r")
                            (and (= (logand mode 16) 16) "w")
                            (and (= (logand mode 32) 32) "x"))
                    (concat (and (= (logand mode 1) 1) "r")
                            (and (= (logand mode 2) 2) "w")
                            (and (= (logand mode 4) 4) "x"))))))
         (eshell-printn modstr))
     (setcar args (eshell-convert (car args)))
     (if (numberp (car args))
         (set-default-file-modes
          (- 511 (car (read-from-string
                       (concat "?\\" (number-to-string (car args)))))))
       (error "setting umask symbolically is not yet implemented"))
     (eshell-print
      "Warning: umask changed for all new files created by Emacs.\n"))
   nil))

(provide 'em-basic)

(require 'pcomplete)

(require 'esh-mode)
(require 'esh-util)

(eval-when-compile
  (require 'cl-lib)
  (require 'eshell))

;;;###autoload
(progn
(defgroup eshell-cmpl nil
  "This module provides a programmable completion function bound to
the TAB key, which allows for completing command names, file names,
variable names, arguments, etc."
  :tag "Argument completion"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-cmpl-load-hook nil
  "A list of functions to run when `eshell-cmpl' is loaded."
  :version "24.1"                       ; removed eshell-cmpl-initialize
  :type 'hook
  :group 'eshell-cmpl)

(defcustom eshell-show-lisp-completions nil
  "If non-nil, include Lisp functions in the command completion list.
If this variable is nil, Lisp completion can still be done in command
position by using M-TAB instead of TAB."
  :type 'boolean
  :group 'eshell-cmpl)

(defcustom eshell-show-lisp-alternatives t
  "If non-nil, and no other completions found, show Lisp functions.
Setting this variable means nothing if `eshell-show-lisp-completions'
is non-nil."
  :type 'boolean
  :group 'eshell-cmpl)

(defcustom eshell-no-completion-during-jobs t
  "If non-nil, don't allow completion while a process is running."
  :type 'boolean
  :group 'eshell-cmpl)

(defcustom eshell-command-completions-alist
  '(("acroread" . "\\.pdf\\'")
    ("xpdf"     . "\\.pdf\\'")
    ("ar"       . "\\.[ao]\\'")
    ("gcc"      . "\\.[Cc]\\([Cc]\\|[Pp][Pp]\\)?\\'")
    ("g++"      . "\\.[Cc]\\([Cc]\\|[Pp][Pp]\\)?\\'")
    ("cc"       . "\\.[Cc]\\([Cc]\\|[Pp][Pp]\\)?\\'")
    ("CC"       . "\\.[Cc]\\([Cc]\\|[Pp][Pp]\\)?\\'")
    ("acc"      . "\\.[Cc]\\([Cc]\\|[Pp][Pp]\\)?\\'")
    ("bcc"      . "\\.[Cc]\\([Cc]\\|[Pp][Pp]\\)?\\'")
    ("readelf"  . "\\(\\`[^.]*\\|\\.\\([ao]\\|so\\)\\)\\'")
    ("objdump"  . "\\(\\`[^.]*\\|\\.\\([ao]\\|so\\)\\)\\'")
    ("nm"       . "\\(\\`[^.]*\\|\\.\\([ao]\\|so\\)\\)\\'")
    ("gdb"      . "\\`\\([^.]*\\|a\\.out\\)\\'")
    ("dbx"      . "\\`\\([^.]*\\|a\\.out\\)\\'")
    ("sdb"      . "\\`\\([^.]*\\|a\\.out\\)\\'")
    ("adb"      . "\\`\\([^.]*\\|a\\.out\\)\\'"))
  "An alist that defines simple argument type correlations.
This is provided for common commands, as a simplistic alternative
to writing a completion function."
  :type '(repeat (cons string regexp))
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-file-ignore "~\\'"
  (documentation-property 'pcomplete-file-ignore
                          'variable-documentation)
  :type (get 'pcomplete-file-ignore 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-dir-ignore "\\`\\(\\.\\.?\\|CVS\\)/\\'"
  (documentation-property 'pcomplete-dir-ignore
                          'variable-documentation)
  :type (get 'pcomplete-dir-ignore 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-ignore-case (eshell-under-windows-p)
  (documentation-property 'pcomplete-ignore-case
                          'variable-documentation)
  :type (get 'pcomplete-ignore-case 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-autolist nil
  (documentation-property 'pcomplete-autolist
                          'variable-documentation)
  :type (get 'pcomplete-autolist 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-suffix-list (list ?/ ?:)
  (documentation-property 'pcomplete-suffix-list
                          'variable-documentation)
  :type (get 'pcomplete-suffix-list 'custom-type)
  :group 'pcomplete)

(defcustom eshell-cmpl-recexact nil
  (documentation-property 'pcomplete-recexact
                          'variable-documentation)
  :type (get 'pcomplete-recexact 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-man-function 'man
  (documentation-property 'pcomplete-man-function
                          'variable-documentation)
  :type (get 'pcomplete-man-function 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-compare-entry-function 'file-newer-than-file-p
  (documentation-property 'pcomplete-compare-entry-function
                          'variable-documentation)
  :type (get 'pcomplete-compare-entry-function 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-expand-before-complete nil
  (documentation-property 'pcomplete-expand-before-complete
                          'variable-documentation)
  :type (get 'pcomplete-expand-before-complete 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-cycle-completions t
  (documentation-property 'pcomplete-cycle-completions
                          'variable-documentation)
  :type (get 'pcomplete-cycle-completions 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-cycle-cutoff-length 5
  (documentation-property 'pcomplete-cycle-cutoff-length
                          'variable-documentation)
  :type (get 'pcomplete-cycle-cutoff-length 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-restore-window-delay 1
  (documentation-property 'pcomplete-restore-window-delay
                          'variable-documentation)
  :type (get 'pcomplete-restore-window-delay 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-command-completion-function
  (function
   (lambda ()
     (pcomplete-here (eshell-complete-commands-list))))
  (documentation-property 'pcomplete-command-completion-function
                          'variable-documentation)
  :type (get 'pcomplete-command-completion-function 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-command-name-function
  'eshell-completion-command-name
  (documentation-property 'pcomplete-command-name-function
                          'variable-documentation)
  :type (get 'pcomplete-command-name-function 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-default-completion-function
  (function
   (lambda ()
     (while (pcomplete-here
             (pcomplete-dirs-or-entries
              (cdr (assoc (funcall eshell-cmpl-command-name-function)
                          eshell-command-completions-alist)))))))
  (documentation-property 'pcomplete-default-completion-function
                          'variable-documentation)
  :type (get 'pcomplete-default-completion-function 'custom-type)
  :group 'eshell-cmpl)

(defcustom eshell-cmpl-use-paring t
  (documentation-property 'pcomplete-use-paring 'variable-documentation)
  :type (get 'pcomplete-use-paring 'custom-type)
  :group 'eshell-cmpl)

;;; Functions:

(defun eshell-complete-lisp-symbol ()
  "Try to complete the text around point as a Lisp symbol."
  (interactive)
  (let ((completion-at-point-functions '(lisp-completion-at-point)))
    (completion-at-point)))

(defun eshell-cmpl-initialize ()
  "Initialize the completions module."
  (set (make-local-variable 'pcomplete-command-completion-function)
       eshell-command-completion-function)
  (set (make-local-variable 'pcomplete-command-name-function)
       eshell-cmpl-command-name-function)
  (set (make-local-variable 'pcomplete-default-completion-function)
       eshell-default-completion-function)
  (set (make-local-variable 'pcomplete-parse-arguments-function)
       'eshell-complete-parse-arguments)
  (set (make-local-variable 'pcomplete-file-ignore)
       eshell-cmpl-file-ignore)
  (set (make-local-variable 'pcomplete-dir-ignore)
       eshell-cmpl-dir-ignore)
  (set (make-local-variable 'pcomplete-ignore-case)
       eshell-cmpl-ignore-case)
  (set (make-local-variable 'pcomplete-autolist)
       eshell-cmpl-autolist)
  (set (make-local-variable 'pcomplete-suffix-list)
       eshell-cmpl-suffix-list)
  (set (make-local-variable 'pcomplete-recexact)
       eshell-cmpl-recexact)
  (set (make-local-variable 'pcomplete-man-function)
       eshell-cmpl-man-function)
  (set (make-local-variable 'pcomplete-compare-entry-function)
       eshell-cmpl-compare-entry-function)
  (set (make-local-variable 'pcomplete-expand-before-complete)
       eshell-cmpl-expand-before-complete)
  (set (make-local-variable 'pcomplete-cycle-completions)
       eshell-cmpl-cycle-completions)
  (set (make-local-variable 'pcomplete-cycle-cutoff-length)
       eshell-cmpl-cycle-cutoff-length)
  (set (make-local-variable 'pcomplete-restore-window-delay)
       eshell-cmpl-restore-window-delay)
  (set (make-local-variable 'pcomplete-use-paring)
       eshell-cmpl-use-paring)
  ;; `comint-file-name-quote-list' should only be set after all the
  ;; load-hooks for any other extension modules have been run, which
  ;; is true at the time `eshell-mode-hook' is run
  (add-hook 'eshell-mode-hook
            (function
             (lambda ()
               (set (make-local-variable 'comint-file-name-quote-list)
                    eshell-special-chars-outside-quoting))) nil t)
  (add-hook 'pcomplete-quote-arg-hook 'eshell-quote-backslash nil t)
  (define-key eshell-mode-map [(meta tab)] 'eshell-complete-lisp-symbol)
  (define-key eshell-mode-map [(meta control ?i)] 'eshell-complete-lisp-symbol)
  (define-key eshell-command-map [(meta ?h)] 'eshell-completion-help)
  (define-key eshell-command-map [tab] 'pcomplete-expand-and-complete)
  (define-key eshell-command-map [(control ?i)]
    'pcomplete-expand-and-complete)
  (define-key eshell-command-map [space] 'pcomplete-expand)
  (define-key eshell-command-map [? ] 'pcomplete-expand)
  (define-key eshell-mode-map [tab] 'eshell-pcomplete)
  (define-key eshell-mode-map [(control ?i)] 'eshell-pcomplete)
  (add-hook 'completion-at-point-functions
            #'pcomplete-completions-at-point nil t)
  ;; jww (1999-10-19): Will this work on anything but X?
  (if (featurep 'xemacs)
      (define-key eshell-mode-map [iso-left-tab] 'pcomplete-reverse)
    (define-key eshell-mode-map [backtab] 'pcomplete-reverse))
  (define-key eshell-mode-map [(meta ??)] 'pcomplete-list))

(defun eshell-completion-command-name ()
  "Return the command name, possibly sans globbing."
  (let ((cmd (file-name-nondirectory (pcomplete-arg 'first))))
    (setq cmd (if (and (> (length cmd) 0)
                       (eq (aref cmd 0) eshell-explicit-command-char))
                  (substring cmd 1)
                cmd))
    (if (eshell-under-windows-p)
        (file-name-sans-extension cmd)
      cmd)))

(defun eshell-completion-help ()
  (interactive)
  (if (= (point) eshell-last-output-end)
      (describe-prefix-bindings)
    (call-interactively 'pcomplete-help)))

(defun eshell-complete-parse-arguments ()
  "Parse the command line arguments for `pcomplete-argument'."
  (when (and eshell-no-completion-during-jobs
             (eshell-interactive-process))
    (insert-and-inherit "\t")
    (throw 'pcompleted t))
  (let ((end (point-marker))
        (begin (save-excursion (eshell-bol) (point)))
        (posns (list t))
        args delim)
    (when (memq this-command '(pcomplete-expand
                               pcomplete-expand-and-complete))
      (run-hook-with-args 'eshell-expand-input-functions begin end)
      (if (= begin end)
          (end-of-line))
      (setq end (point-marker)))
    (if (setq delim
              (catch 'eshell-incomplete
                (ignore
                 (setq args (eshell-parse-arguments begin end)))))
        (cond ((memq (car delim) '(?\{ ?\<))
               (setq begin (1+ (cadr delim))
                     args (eshell-parse-arguments begin end)))
              ((eq (car delim) ?\()
               (eshell-complete-lisp-symbol)
               (throw 'pcompleted t))
              (t
               (insert-and-inherit "\t")
               (throw 'pcompleted t))))
    (when (get-text-property (1- end) 'comment)
      (insert-and-inherit "\t")
      (throw 'pcompleted t))
    (let ((pos begin))
      (while (< pos end)
        (if (get-text-property pos 'arg-begin)
            (nconc posns (list pos)))
        (setq pos (1+ pos))))
    (setq posns (cdr posns))
    (cl-assert (= (length args) (length posns)))
    (let ((a args)
          (i 0)
          l)
      (while a
        (if (and (consp (car a))
                 (eq (caar a) 'eshell-operator))
            (setq l i))
        (setq a (cdr a) i (1+ i)))
      (and l
           (setq args (nthcdr (1+ l) args)
                 posns (nthcdr (1+ l) posns))))
    (cl-assert (= (length args) (length posns)))
    (when (and args (eq (char-syntax (char-before end)) ? )
               (not (eq (char-before (1- end)) ?\\)))
      (nconc args (list ""))
      (nconc posns (list (point))))
    (cons (mapcar
           (function
            (lambda (arg)
              (let ((val
                     (if (listp arg)
                         (let ((result
                                (eshell-do-eval
                                 (list 'eshell-commands arg) t)))
                           (cl-assert (eq (car result) 'quote))
                           (cadr result))
                       arg)))
                (if (numberp val)
                    (setq val (number-to-string val)))
                (or val ""))))
           args)
          posns)))

(defun eshell-complete-commands-list ()
  "Generate list of applicable, visible commands."
  (let ((filename (pcomplete-arg)) glob-name)
    (if (file-name-directory filename)
        (pcomplete-executables)
      (if (and (> (length filename) 0)
               (eq (aref filename 0) eshell-explicit-command-char))
          (setq filename (substring filename 1)
                pcomplete-stub filename
                glob-name t))
      (let* ((paths (eshell-parse-colon-path eshell-path-env))
             (cwd (file-name-as-directory
                   (expand-file-name default-directory)))
             (path "") (comps-in-path ())
             (file "") (filepath "") (completions ()))
        ;; Go thru each path in the search path, finding completions.
        (while paths
          (setq path (file-name-as-directory
                      (expand-file-name (or (car paths) ".")))
                comps-in-path
                (and (file-accessible-directory-p path)
                     (file-name-all-completions filename path)))
          ;; Go thru each completion found, to see whether it should
          ;; be used.
          (while comps-in-path
            (setq file (car comps-in-path)
                  filepath (concat path file))
            (if (and (not (member file completions)) ;
                     (or (string-equal path cwd)
                         (not (file-directory-p filepath)))
                     (file-executable-p filepath))
                (setq completions (cons file completions)))
            (setq comps-in-path (cdr comps-in-path)))
          (setq paths (cdr paths)))
        ;; Add aliases which are currently visible, and Lisp functions.
        (pcomplete-uniqify-list
         (if glob-name
             completions
           (setq completions
                 (append (and (eshell-using-module 'eshell-alias)
                              (funcall (symbol-function 'eshell-alias-completions)
                                       filename))
                         (eshell-winnow-list
                          (mapcar
                           (function
                            (lambda (name)
                              (substring name 7)))
                           (all-completions (concat "eshell/" filename)
                                            obarray 'functionp))
                          nil '(eshell-find-alias-function))
                         completions))
           (append (and (or eshell-show-lisp-completions
                            (and eshell-show-lisp-alternatives
                                 (null completions)))
                        (all-completions filename obarray 'functionp))
                   completions)))))))

(defun eshell-pcomplete (&optional interactively)
  "Eshell wrapper for `pcomplete'."
  (interactive "p")
  ;; Pretend to be pcomplete so that cycling works (bug#13293).
  (setq this-command 'pcomplete)
  (condition-case nil
      (if interactively
          (call-interactively 'pcomplete)
        (pcomplete))
    (text-read-only (completion-at-point)))) ; Workaround for bug#12838.

(provide 'em-cmpl)

;;; Code:

(require 'eshell)
(require 'ring)
(require 'esh-opt)

;;;###autoload
(progn
(defgroup eshell-dirs nil
  "Directory navigation involves changing directories, examining the
current directory, maintaining a directory stack, and also keeping
track of a history of the last directory locations the user was in.
Emacs does provide standard Lisp definitions of `pwd' and `cd', but
they lack somewhat in feel from the typical shell equivalents."
  :tag "Directory navigation"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-dirs-load-hook nil
  "A hook that gets run when `eshell-dirs' is loaded."
  :version "24.1"                       ; removed eshell-dirs-initialize
  :type 'hook
  :group 'eshell-dirs)

(defcustom eshell-pwd-convert-function (if (eshell-under-windows-p)
                                           'expand-file-name
                                         'identity)
  "The function used to normalize the value of Eshell's `pwd'.
The value returned by `pwd' is also used when recording the
last-visited directory in the last-dir-ring, so it will affect the
form of the list used by 'cd ='."
  :type '(radio (function-item file-truename)
                (function-item expand-file-name)
                (function-item identity)
                (function :tag "Other"))
  :group 'eshell-dirs)

(defcustom eshell-ask-to-save-last-dir 'always
  "Determine if the last-dir-ring should be automatically saved.
The last-dir-ring is always preserved when exiting an Eshell buffer.
However, when Emacs is being shut down, this variable determines
whether to prompt the user, or just save the ring.
If set to nil, it means never ask whether to save the last-dir-ring.
If set to t, always ask if any Eshell buffers are open at exit time.
If set to `always', the list-dir-ring will always be saved, silently."
  :type '(choice (const :tag "Never" nil)
                 (const :tag "Ask" t)
                 (const :tag "Always save" always))
  :group 'eshell-dirs)

(defcustom eshell-cd-shows-directory nil
  "If non-nil, using `cd' will report the directory it changes to."
  :type 'boolean
  :group 'eshell-dirs)

(defcustom eshell-cd-on-directory t
  "If non-nil, do a cd if a directory is in command position."
  :type 'boolean
  :group 'eshell-dirs)

(defcustom eshell-directory-change-hook nil
  "A hook to run when the current directory changes."
  :type 'hook
  :group 'eshell-dirs)

(defcustom eshell-list-files-after-cd nil
  "If non-nil, call \"ls\" with any remaining args after doing a cd.
This is provided for convenience, since the same effect is easily
achieved by adding a function to `eshell-directory-change-hook' that
calls \"ls\" and references `eshell-last-arguments'."
  :type 'boolean
  :group 'eshell-dirs)

(defcustom eshell-pushd-tohome nil
  "If non-nil, make pushd with no arg behave as 'pushd ~' (like `cd').
This mirrors the optional behavior of tcsh."
  :type 'boolean
  :group 'eshell-dirs)

(defcustom eshell-pushd-dextract nil
  "If non-nil, make \"pushd +n\" pop the nth dir to the stack top.
This mirrors the optional behavior of tcsh."
  :type 'boolean
  :group 'eshell-dirs)

(defcustom eshell-pushd-dunique nil
  "If non-nil, make pushd only add unique directories to the stack.
This mirrors the optional behavior of tcsh."
  :type 'boolean
  :group 'eshell-dirs)

(defcustom eshell-dirtrack-verbose t
  "If non-nil, show the directory stack following directory change.
This is effective only if directory tracking is enabled."
  :type 'boolean
  :group 'eshell-dirs)

(defcustom eshell-last-dir-ring-file-name
  (expand-file-name "lastdir" eshell-directory-name)
  "If non-nil, name of the file to read/write the last-dir-ring.
See also `eshell-read-last-dir-ring' and `eshell-write-last-dir-ring'.
If it is nil, the last-dir-ring will not be written to disk."
  :type 'file
  :group 'eshell-dirs)

(defcustom eshell-last-dir-ring-size 32
  "If non-nil, the size of the directory history ring.
This ring is added to every time `cd' or `pushd' is used.  It simply
stores the most recent directory locations Eshell has been in.  To
return to the most recent entry, use 'cd -' (equivalent to 'cd -0').
To return to an older entry, use 'cd -N', where N is an integer less
than `eshell-last-dir-ring-size'.  To return to the last directory
matching a particular regexp, use 'cd =REGEXP'.  To display the
directory history list, use 'cd ='.

This mechanism is very similar to that provided by `pushd', except
it's far more automatic.  `pushd' allows the user to decide which
directories gets pushed, and its size is unlimited.

`eshell-last-dir-ring' is meant for users who don't use `pushd'
explicitly very much, but every once in a while would like to return to
a previously visited directory without having to type in the whole
thing again."
  :type 'integer
  :group 'eshell-dirs)

(defcustom eshell-last-dir-unique t
  "If non-nil, `eshell-last-dir-ring' contains only unique entries."
  :type 'boolean
  :group 'eshell-dirs)

;;; Internal Variables:

(defvar eshell-dirstack nil
  "List of directories saved by pushd in the Eshell buffer.
Thus, this does not include the current directory.")

(defvar eshell-last-dir-ring nil
  "The last directory that Eshell was in.")

;;; Functions:

(defun eshell-dirs-initialize ()
  "Initialize the builtin functions for Eshell."
  (make-local-variable 'eshell-variable-aliases-list)
  (setq eshell-variable-aliases-list
        (append
         eshell-variable-aliases-list
         '(("-" (lambda (indices)
                  (if (not indices)
                      (unless (ring-empty-p eshell-last-dir-ring)
                        (expand-file-name
                         (ring-ref eshell-last-dir-ring 0)))
                    (expand-file-name
                     (eshell-apply-indices eshell-last-dir-ring indices)))))
           ("+" "PWD")
           ("PWD" (lambda (indices)
                    (expand-file-name (eshell/pwd))) t)
           ("OLDPWD" (lambda (indices)
                       (unless (ring-empty-p eshell-last-dir-ring)
                         (expand-file-name
                          (ring-ref eshell-last-dir-ring 0)))) t))))

  (when eshell-cd-on-directory
    (make-local-variable 'eshell-interpreter-alist)
    (setq eshell-interpreter-alist
          (cons (cons #'(lambda (file args)
                          (eshell-lone-directory-p file))
                      'eshell-dirs-substitute-cd)
                eshell-interpreter-alist)))

  (add-hook 'eshell-parse-argument-hook
            'eshell-parse-user-reference nil t)
  (if (eshell-under-windows-p)
      (add-hook 'eshell-parse-argument-hook
                'eshell-parse-drive-letter nil t))

  (when (eshell-using-module 'eshell-cmpl)
    (add-hook 'pcomplete-try-first-hook
              'eshell-complete-user-reference nil t))

  (make-local-variable 'eshell-dirstack)
  (make-local-variable 'eshell-last-dir-ring)

  (if eshell-last-dir-ring-file-name
      (eshell-read-last-dir-ring))
  (unless eshell-last-dir-ring
    (setq eshell-last-dir-ring (make-ring eshell-last-dir-ring-size)))

  (add-hook 'eshell-exit-hook 'eshell-write-last-dir-ring nil t)

  (add-hook 'kill-emacs-hook 'eshell-save-some-last-dir))

(defun eshell-save-some-last-dir ()
  "Save the list-dir-ring for any open Eshell buffers."
  (dolist (buf (buffer-list))
    (if (buffer-live-p buf)
        (with-current-buffer buf
          (if (and eshell-mode
                   eshell-ask-to-save-last-dir
                   (or (eq eshell-ask-to-save-last-dir 'always)
                       (y-or-n-p
                        (format "Save last dir ring for Eshell buffer `%s'? "
                                (buffer-name buf)))))
              (eshell-write-last-dir-ring))))))

(defun eshell-lone-directory-p (file)
  "Test whether FILE is just a directory name, and not a command name."
  (and (file-directory-p file)
       (or (file-name-directory file)
           (not (eshell-search-path file)))))

(defun eshell-dirs-substitute-cd (&rest args)
  "Substitute the given command for a call to `cd' on that name."
  (if (> (length args) 1)
      (error "%s: command not found" (car args))
    (throw 'eshell-replace-command
           (eshell-parse-command "cd" (eshell-flatten-list args)))))

(defun eshell-parse-user-reference ()
  "An argument beginning with ~ is a filename to be expanded."
  (when (and (not eshell-current-argument)
             (eq (char-after) ?~))
    (add-to-list 'eshell-current-modifiers 'expand-file-name)
    (forward-char)
    (char-to-string (char-before))))

(defun eshell-parse-drive-letter ()
  "An argument beginning with X:[^/] is a drive letter reference."
  (when (and (not eshell-current-argument)
             (looking-at "\\([A-Za-z]:\\)\\([^/\\\\]\\|\\'\\)"))
    (goto-char (match-end 1))
    (let* ((letter (match-string 1))
           (regexp (concat "\\`" letter))
           (path (eshell-find-previous-directory regexp)))
      (concat (or path letter) "/"))))

(defvar pcomplete-stub)
(defvar pcomplete-last-completion-raw)
(declare-function pcomplete-actual-arg "pcomplete")
(declare-function pcomplete-uniqify-list "pcomplete")

(defun eshell-complete-user-reference ()
  "If there is a user reference, complete it."
  (let ((arg (pcomplete-actual-arg)))
    (when (string-match "\\`~[a-z]*\\'" arg)
      (setq pcomplete-stub (substring arg 1)
            pcomplete-last-completion-raw t)
      (throw 'pcomplete-completions
             (progn
               (eshell-read-user-names)
               (pcomplete-uniqify-list
                (mapcar
                 (function
                  (lambda (user)
                    (file-name-as-directory (cdr user))))
                 eshell-user-names)))))))

(defun eshell/pwd (&rest args)
  "Change output from `pwd` to be cleaner."
  (let* ((path default-directory)
         (len (length path)))
    (if (and (> len 1)
             (eq (aref path (1- len)) ?/)
             (not (and (eshell-under-windows-p)
                       (string-match "\\`[A-Za-z]:[\\\\/]\\'" path))))
        (setq path (substring path 0 (1- (length path)))))
    (if eshell-pwd-convert-function
        (funcall eshell-pwd-convert-function path)
      path)))

(defun eshell-expand-multiple-dots (path)
  "Convert '...' to '../..', '....' to '../../..', etc..

With the following piece of advice, you can make this functionality
available in most of Emacs, with the exception of filename completion
in the minibuffer:

  (defadvice expand-file-name
    (before translate-multiple-dots
            (filename &optional directory) activate)
    (setq filename (eshell-expand-multiple-dots filename)))"
  (while (string-match "\\(?:^\\|/\\)\\.\\.\\(\\.+\\)\\(?:$\\|/\\)" path)
    (let* ((extra-dots (match-string 1 path))
           (len (length extra-dots))
           replace-text)
      (while (> len 0)
        (setq replace-text (concat replace-text "/..")
              len (1- len)))
      (setq path
            (replace-match replace-text t t path 1))))
  path)

(defun eshell-find-previous-directory (regexp)
  "Find the most recent last-dir matching REGEXP."
  (let ((index 0)
        (len (ring-length eshell-last-dir-ring))
        oldpath)
    (if (> (length regexp) 0)
        (while (< index len)
          (setq oldpath (ring-ref eshell-last-dir-ring index))
          (if (string-match regexp oldpath)
              (setq index len)
            (setq oldpath nil
                  index (1+ index)))))
    oldpath))

(defvar dired-directory)

(defun eshell/cd (&rest args)           ; all but first ignored
  "Alias to extend the behavior of `cd'."
  (setq args (eshell-flatten-list args))
  (let ((path (car args))
        (subpath (car (cdr args)))
        (case-fold-search (eshell-under-windows-p))
        handled)
    (if (numberp path)
        (setq path (number-to-string path)))
    (if (numberp subpath)
        (setq subpath (number-to-string subpath)))
    (cond
     (subpath
      (let ((curdir (eshell/pwd)))
        (if (string-match path curdir)
            (setq path (replace-match subpath nil nil curdir))
          (error "Path substring '%s' not found" path))))
     ((and path (string-match "^-\\([0-9]*\\)$" path))
      (let ((index (match-string 1 path)))
        (setq path
              (ring-remove eshell-last-dir-ring
                           (if index
                               (string-to-number index)
                             0)))))
     ((and path (string-match "^=\\(.*\\)$" path))
      (let ((oldpath (eshell-find-previous-directory
                      (match-string 1 path))))
        (if oldpath
            (setq path oldpath)
          (let ((len (ring-length eshell-last-dir-ring))
                (index 0))
            (if (= len 0)
                (error "Directory ring empty"))
            (eshell-init-print-buffer)
            (while (< index len)
              (eshell-buffered-print
               (concat (number-to-string index) ": "
                       (ring-ref eshell-last-dir-ring index) "\n"))
              (setq index (1+ index)))
            (eshell-flush)
            (setq handled t)))))
     (path
      (setq path (eshell-expand-multiple-dots path))))
    (unless handled
      (setq dired-directory (or path "~"))
      (let ((curdir (eshell/pwd)))
        (unless (equal curdir dired-directory)
          (eshell-add-to-dir-ring curdir))
        (let ((result (cd dired-directory)))
          (and eshell-cd-shows-directory
               (eshell-printn result)))
        (run-hooks 'eshell-directory-change-hook)
        (if eshell-list-files-after-cd
            ;; Let-bind eshell-last-command around this?
            (eshell-plain-command "ls" (cdr args)))
        nil))))

(put 'eshell/cd 'eshell-no-numeric-conversions t)

(defun eshell-add-to-dir-ring (path)
  "Add PATH to the last-dir-ring, if applicable."
  (unless (and (not (ring-empty-p eshell-last-dir-ring))
               (equal path (ring-ref eshell-last-dir-ring 0)))
    (if eshell-last-dir-unique
        (let ((index 0)
              (len (ring-length eshell-last-dir-ring)))
          (while (< index len)
            (if (equal (ring-ref eshell-last-dir-ring index) path)
                (ring-remove eshell-last-dir-ring index)
              (setq index (1+ index))))))
    (ring-insert eshell-last-dir-ring path)))

;;; pushd [+n | dir]
(defun eshell/pushd (&rest args)        ; all but first ignored
  "Implementation of pushd in Lisp."
  (let ((path (car args)))
    (cond
     ((null path)
      ;; no arg -- swap pwd and car of stack unless eshell-pushd-tohome
      (cond (eshell-pushd-tohome
             (eshell/pushd "~"))
            (eshell-dirstack
             (let ((old (eshell/pwd)))
               (eshell/cd (car eshell-dirstack))
               (setq eshell-dirstack (cons old (cdr eshell-dirstack)))
               (eshell/dirs t)))
            (t
             (error "pushd: No other directory"))))
     ((string-match "^\\+\\([0-9]\\)" path)
      ;; pushd +n
      (setq path (string-to-number (match-string 1 path)))
      (cond ((> path (length eshell-dirstack))
             (error "Directory stack not that deep"))
            ((= path 0)
             (error "Couldn't cd"))
            (eshell-pushd-dextract
             (let ((dir (nth (1- path) eshell-dirstack)))
               (eshell/popd path)
               (eshell/pushd (eshell/pwd))
               (eshell/cd dir)
               (eshell/dirs t)))
            (t
             (let* ((ds (cons (eshell/pwd) eshell-dirstack))
                    (dslen (length ds))
                    (front (nthcdr path ds))
                    (back (nreverse (nthcdr (- dslen path) (reverse ds))))
                    (new-ds (append front back)))
               (eshell/cd (car new-ds))
               (setq eshell-dirstack (cdr new-ds))
               (eshell/dirs t)))))
     (t
      ;; pushd <dir>
      (let ((old-wd (eshell/pwd)))
        (eshell/cd path)
        (if (or (null eshell-pushd-dunique)
                (not (member old-wd eshell-dirstack)))
            (setq eshell-dirstack (cons old-wd eshell-dirstack)))
        (eshell/dirs t)))))
  nil)

(put 'eshell/pushd 'eshell-no-numeric-conversions t)

;;; popd [+n]
(defun eshell/popd (&rest args)
  "Implementation of popd in Lisp."
  (let ((ref (or (car args) "+0")))
    (unless (and (stringp ref)
                 (string-match "\\`\\([+-][0-9]+\\)\\'" ref))
      (error "popd: bad arg `%s'" ref))
    (setq ref (string-to-number (match-string 1 ref)))
    (cond ((= ref 0)
           (unless eshell-dirstack
             (error "popd: Directory stack empty"))
           (eshell/cd (car eshell-dirstack))
           (setq eshell-dirstack (cdr eshell-dirstack))
           (eshell/dirs t))
          ((<= (abs ref) (length eshell-dirstack))
           (let* ((ds (cons nil eshell-dirstack))
                  (cell (nthcdr (if (> ref 0)
                                    (1- ref)
                                  (+ (length eshell-dirstack) ref)) ds))
                  (dir (cadr cell)))
             (eshell/cd dir)
             (setcdr cell (cdr (cdr cell)))
             (setq eshell-dirstack (cdr ds))
             (eshell/dirs t)))
          (t
           (error "Couldn't popd"))))
  nil)

(put 'eshell/popd 'eshell-no-numeric-conversions t)

(defun eshell/dirs (&optional if-verbose)
  "Implementation of dirs in Lisp."
  (when (or (not if-verbose) eshell-dirtrack-verbose)
    (let* ((msg "")
           (ds (cons (eshell/pwd) eshell-dirstack))
           (home (expand-file-name "~/"))
           (homelen (length home)))
      (while ds
        (let ((dir (car ds)))
          (and (>= (length dir) homelen)
               (string= home (substring dir 0 homelen))
               (setq dir (concat "~/" (substring dir homelen))))
          (setq msg (concat msg (directory-file-name dir) " "))
          (setq ds (cdr ds))))
      msg)))

(defun eshell-read-last-dir-ring ()
  "Set the buffer's `eshell-last-dir-ring' from a history file."
  (let ((file eshell-last-dir-ring-file-name))
    (cond
     ((or (null file)
          (equal file "")
          (not (file-readable-p file)))
      nil)
     (t
      (let* ((count 0)
             (size eshell-last-dir-ring-size)
             (ring (make-ring size)))
        (with-temp-buffer
          (insert-file-contents file)
          ;; Save restriction in case file is already visited...
          ;; Watch for those date stamps in history files!
          (goto-char (point-max))
          (while (and (< count size)
                      (re-search-backward "^\\([^\n].*\\)$" nil t))
            (ring-insert-at-beginning ring (match-string 1))
            (setq count (1+ count)))
          ;; never allow the top element to equal the current
          ;; directory
          (while (and (not (ring-empty-p ring))
                      (equal (ring-ref ring 0) (eshell/pwd)))
            (ring-remove ring 0)))
        (setq eshell-last-dir-ring ring))))))

(defun eshell-write-last-dir-ring ()
  "Write the buffer's `eshell-last-dir-ring' to a history file."
  (let ((file eshell-last-dir-ring-file-name))
    (cond
     ((or (null file)
          (equal file "")
          (null eshell-last-dir-ring)
          (ring-empty-p eshell-last-dir-ring))
      nil)
     ((not (file-writable-p file))
      (message "Cannot write last-dir-ring file %s" file))
     (t
      (let* ((ring eshell-last-dir-ring)
             (index (ring-length ring)))
        (with-temp-buffer
          (while (> index 0)
            (setq index (1- index))
            (insert (ring-ref ring index) ?\n))
          (insert (eshell/pwd) ?\n)
          (eshell-with-private-file-modes
           (write-region (point-min) (point-max) file nil
                         'no-message))))))))

(provide 'em-dirs)

;; Local Variables:
;; generated-autoload-file: "esh-groups.el"
;; End:

;;; em-dirs.el ends here

(require 'esh-util)
(require 'esh-arg)
(eval-when-compile (require 'eshell))

;;;###autoload
(progn
(defgroup eshell-pred nil
  "This module allows for predicates to be applied to globbing
patterns (similar to zsh), in addition to string modifiers which can
be applied either to globbing results, variable references, or just
ordinary strings."
  :tag "Value modifiers and predicates"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-pred-load-hook nil
  "A list of functions to run when `eshell-pred' is loaded."
  :version "24.1"                       ; removed eshell-pred-initialize
  :type 'hook
  :group 'eshell-pred)

(defcustom eshell-predicate-alist
  '((?/ . (eshell-pred-file-type ?d))   ; directories
    (?. . (eshell-pred-file-type ?-))   ; regular files
    (?s . (eshell-pred-file-type ?s))   ; sockets
    (?p . (eshell-pred-file-type ?p))   ; named pipes
    (?@ . (eshell-pred-file-type ?l))   ; symbolic links
    (?% . (eshell-pred-file-type ?%))   ; allow user to specify (c def.)
    (?r . (eshell-pred-file-mode 0400)) ; owner-readable
    (?w . (eshell-pred-file-mode 0200)) ; owner-writable
    (?x . (eshell-pred-file-mode 0100)) ; owner-executable
    (?A . (eshell-pred-file-mode 0040)) ; group-readable
    (?I . (eshell-pred-file-mode 0020)) ; group-writable
    (?E . (eshell-pred-file-mode 0010)) ; group-executable
    (?R . (eshell-pred-file-mode 0004)) ; world-readable
    (?W . (eshell-pred-file-mode 0002)) ; world-writable
    (?X . (eshell-pred-file-mode 0001)) ; world-executable
    (?s . (eshell-pred-file-mode 4000)) ; setuid
    (?S . (eshell-pred-file-mode 2000)) ; setgid
    (?t . (eshell-pred-file-mode 1000)) ; sticky bit
    (?U . #'(lambda (file)                   ; owned by effective uid
              (if (file-exists-p file)
                  (= (nth 2 (file-attributes file)) (user-uid)))))
    ;; (?G . #'(lambda (file)               ; owned by effective gid
    ;;          (if (file-exists-p file)
    ;;              (= (nth 2 (file-attributes file)) (user-uid)))))
    (?* . #'(lambda (file)
              (and (file-regular-p file)
                   (not (file-symlink-p file))
                   (file-executable-p file))))
    (?l . (eshell-pred-file-links))
    (?u . (eshell-pred-user-or-group ?u "user" 2 'eshell-user-id))
    (?g . (eshell-pred-user-or-group ?g "group" 3 'eshell-group-id))
    (?a . (eshell-pred-file-time ?a "access" 4))
    (?m . (eshell-pred-file-time ?m "modification" 5))
    (?c . (eshell-pred-file-time ?c "change" 6))
    (?L . (eshell-pred-file-size)))
  "A list of predicates than can be applied to a globbing pattern.
The format of each entry is

  (CHAR . PREDICATE-FUNC-SEXP)"
  :type '(repeat (cons character sexp))
  :group 'eshell-pred)

(put 'eshell-predicate-alist 'risky-local-variable t)

(defcustom eshell-modifier-alist
  '((?E . #'(lambda (lst)
              (mapcar
               (function
                (lambda (str)
                  (eshell-stringify
                   (car (eshell-parse-argument str))))) lst)))
    (?L . #'(lambda (lst) (mapcar 'downcase lst)))
    (?U . #'(lambda (lst) (mapcar 'upcase lst)))
    (?C . #'(lambda (lst) (mapcar 'capitalize lst)))
    (?h . #'(lambda (lst) (mapcar 'file-name-directory lst)))
    (?i . (eshell-include-members))
    (?x . (eshell-include-members t))
    (?r . #'(lambda (lst) (mapcar 'file-name-sans-extension lst)))
    (?e . #'(lambda (lst) (mapcar 'file-name-extension lst)))
    (?t . #'(lambda (lst) (mapcar 'file-name-nondirectory lst)))
    (?q . #'(lambda (lst) (mapcar 'eshell-escape-arg lst)))
    (?u . #'(lambda (lst) (eshell-uniqify-list lst)))
    (?o . #'(lambda (lst) (sort lst 'string-lessp)))
    (?O . #'(lambda (lst) (nreverse (sort lst 'string-lessp))))
    (?j . (eshell-join-members))
    (?S . (eshell-split-members))
    (?R . 'reverse)
    (?g . (progn
            (forward-char)
            (if (eq (char-before) ?s)
                (eshell-pred-substitute t)
              (error "`g' modifier cannot be used alone"))))
    (?s . (eshell-pred-substitute)))
  "A list of modifiers than can be applied to an argument expansion.
The format of each entry is

  (CHAR ENTRYWISE-P MODIFIER-FUNC-SEXP)"
  :type '(repeat (cons character sexp))
  :group 'eshell-pred)

(put 'eshell-modifier-alist 'risky-local-variable t)

(defvar eshell-predicate-help-string
  "Eshell predicate quick reference:

  -  follow symbolic references for predicates after the `-'
  ^  invert sense of predicates after the `^'

FILE TYPE:
  /  directories              s  sockets
  .  regular files            p  named pipes
  *  executable (files only)  @  symbolic links

  %x  file type == `x' (as by ls -l; so `c' = char device, etc.)

PERMISSION BITS (for owner/group/world):
  r/A/R  readable    s  setuid
  w/I/W  writable    S  setgid
  x/E/X  executable  t  sticky bit

OWNERSHIP:
  U               owned by effective uid
  u(UID|'user')   owned by UID/user
  g(GID|'group')  owned by GID/group

FILE ATTRIBUTES:
  l[+-]N                 +/-/= N links
  a[Mwhms][+-](N|'FILE') access time +/-/= N months/weeks/hours/mins/secs
                         (days if unspecified) if FILE specified,
                         use as comparison basis; so a+'file.c'
                         shows files accessed before file.c was
                         last accessed
  m[Mwhms][+-](N|'FILE') modification time...
  c[Mwhms][+-](N|'FILE') change time...
  L[kmp][+-]N            file size +/-/= N Kb/Mb/blocks

EXAMPLES:
  *(^@)         all non-dot files which are not symlinks
  .#*(^@)       all files which are not symbolic links
  **/.#*(*)     all executable files, searched recursively
  ***/*~f*(-/)  recursively (though not traversing symlinks),
                find all directories (or symlinks referring to
                directories) whose names do not begin with f.
  e*(*Lk+50)    executables 50k or larger beginning with 'e'")

(defvar eshell-modifier-help-string
  "Eshell modifier quick reference:

FOR SINGLE ARGUMENTS, or each argument of a list of strings:
  E  evaluate again
  L  lowercase
  U  uppercase
  C  capitalize
  h  dirname
  t  basename
  e  file extension
  r  strip file extension
  q  escape special characters

  S       split string at any whitespace character
  S/PAT/  split string at each occurrence of PAT

FOR LISTS OF ARGUMENTS:
  o  sort alphabetically
  O  reverse sort alphabetically
  u  uniq list (typically used after :o or :O)
  R  reverse list

  j       join list members, separated by a space
  j/PAT/  join list members, separated by PAT
  i/PAT/  exclude all members not matching PAT
  x/PAT/  exclude all members matching PAT

  s/pat/match/  substitute PAT with MATCH
  g/pat/match/  substitute PAT with MATCH for all occurrences

EXAMPLES:
  *.c(:o)  sorted list of .c files")

;;; Functions:

(defun eshell-display-predicate-help ()
  (interactive)
  (with-electric-help
   (function
    (lambda ()
      (insert eshell-predicate-help-string)))))

(defun eshell-display-modifier-help ()
  (interactive)
  (with-electric-help
   (function
    (lambda ()
      (insert eshell-modifier-help-string)))))

(defun eshell-pred-initialize ()
  "Initialize the predicate/modifier code."
  (add-hook 'eshell-parse-argument-hook
            'eshell-parse-arg-modifier t t)
  (define-key eshell-command-map [(meta ?q)] 'eshell-display-predicate-help)
  (define-key eshell-command-map [(meta ?m)] 'eshell-display-modifier-help))

(defun eshell-apply-modifiers (lst predicates modifiers)
  "Apply to LIST a series of PREDICATES and MODIFIERS."
  (let (stringified)
    (if (stringp lst)
        (setq lst (list lst)
              stringified t))
    (when (listp lst)
      (setq lst (eshell-winnow-list lst nil predicates))
      (while modifiers
        (setq lst (funcall (car modifiers) lst)
              modifiers (cdr modifiers)))
      (if (and stringified
               (= (length lst) 1))
          (car lst)
        lst))))

(defun eshell-parse-arg-modifier ()
  "Parse a modifier that has been specified after an argument.
This function is specially for adding onto `eshell-parse-argument-hook'."
  (when (eq (char-after) ?\()
    (forward-char)
    (let ((end (eshell-find-delimiter ?\( ?\))))
      (if (not end)
          (throw 'eshell-incomplete ?\()
        (when (eshell-arg-delimiter (1+ end))
          (save-restriction
            (narrow-to-region (point) end)
            (let* ((modifiers (eshell-parse-modifiers))
                   (preds (car modifiers))
                   (mods (cdr modifiers)))
              (if (or preds mods)
                  ;; has to go at the end, which is only natural since
                  ;; syntactically it can only occur at the end
                  (setq eshell-current-modifiers
                        (append
                         eshell-current-modifiers
                         (list
                          `(lambda (lst)
                             (eshell-apply-modifiers
                              lst (quote ,preds) (quote ,mods)))))))))
          (goto-char (1+ end))
          (eshell-finish-arg))))))

(defun eshell-parse-modifiers ()
  "Parse value modifiers and predicates at point.
If ALLOW-PREDS is non-nil, predicates will be parsed as well.
Return a cons cell of the form

  (PRED-FUNC-LIST . MOD-FUNC-LIST)

NEW-STRING is STRING minus any modifiers.  PRED-FUNC-LIST is a list of
predicate functions.  MOD-FUNC-LIST is a list of result modifier
functions.  PRED-FUNCS take a filename and return t if the test
succeeds; MOD-FUNCS take any string and preform a modification,
returning the resultant string."
  (let (negate follow preds mods)
    (condition-case nil
        (while (not (eobp))
          (let ((char (char-after)))
            (cond
             ((eq char ?')
              (forward-char)
              (if (looking-at "[^|':]")
                  (let ((func (read (current-buffer))))
                    (if (and func (functionp func))
                        (setq preds (eshell-add-pred-func func preds
                                                          negate follow))
                      (error "Invalid function predicate '%s'"
                             (eshell-stringify func))))
                (error "Invalid function predicate")))
             ((eq char ?^)
              (forward-char)
              (setq negate (not negate)))
             ((eq char ?-)
              (forward-char)
              (setq follow (not follow)))
             ((eq char ?|)
              (forward-char)
              (if (looking-at "[^|':]")
                  (let ((func (read (current-buffer))))
                    (if (and func (functionp func))
                        (setq mods
                              (cons `(lambda (lst)
                                       (mapcar (function ,func) lst))
                                    mods))
                      (error "Invalid function modifier '%s'"
                             (eshell-stringify func))))
                (error "Invalid function modifier")))
             ((eq char ?:)
              (forward-char)
              (let ((mod (assq (char-after) eshell-modifier-alist)))
                (if (not mod)
                    (error "Unknown modifier character '%c'" (char-after))
                  (forward-char)
                  (setq mods (cons (eval (cdr mod)) mods)))))
             (t
              (let ((pred (assq char eshell-predicate-alist)))
                (if (not pred)
                    (error "Unknown predicate character '%c'" char)
                  (forward-char)
                  (setq preds
                        (eshell-add-pred-func (eval (cdr pred)) preds
                                              negate follow))))))))
      (end-of-buffer
       (error "Predicate or modifier ended prematurely")))
    (cons (nreverse preds) (nreverse mods))))

(defun eshell-add-pred-func (pred funcs negate follow)
  "Add the predicate function PRED to FUNCS."
  (if negate
      (setq pred `(lambda (file)
                    (not (funcall ,pred file)))))
  (if follow
      (setq pred `(lambda (file)
                    (funcall ,pred (file-truename file)))))
  (cons pred funcs))

(defun eshell-pred-user-or-group (mod-char mod-type attr-index get-id-func)
  "Return a predicate to test whether a file match a given user/group id."
  (let (ugid open close end)
    (if (looking-at "[0-9]+")
        (progn
          (setq ugid (string-to-number (match-string 0)))
          (goto-char (match-end 0)))
      (setq open (char-after))
      (if (setq close (memq open '(?\( ?\[ ?\< ?\{)))
          (setq close (car (last '(?\) ?\] ?\> ?\})
                                 (length close))))
        (setq close open))
      (forward-char)
      (setq end (eshell-find-delimiter open close))
      (unless end
        (error "Malformed %s name string for modifier `%c'"
               mod-type mod-char))
      (setq ugid
            (funcall get-id-func (buffer-substring (point) end)))
      (goto-char (1+ end)))
    (unless ugid
      (error "Unknown %s name specified for modifier `%c'"
             mod-type mod-char))
    `(lambda (file)
       (let ((attrs (file-attributes file)))
         (if attrs
             (= (nth ,attr-index attrs) ,ugid))))))

(defun eshell-pred-file-time (mod-char mod-type attr-index)
  "Return a predicate to test whether a file matches a certain time."
  (let* ((quantum 86400)
         qual when open close end)
    (when (memq (char-after) '(?M ?w ?h ?m ?s))
      (setq quantum (char-after))
      (cond
       ((eq quantum ?M)
        (setq quantum (* 60 60 24 30)))
       ((eq quantum ?w)
        (setq quantum (* 60 60 24 7)))
       ((eq quantum ?h)
        (setq quantum (* 60 60)))
       ((eq quantum ?m)
        (setq quantum 60))
       ((eq quantum ?s)
        (setq quantum 1)))
      (forward-char))
    (when (memq (char-after) '(?+ ?-))
      (setq qual (char-after))
      (forward-char))
    (if (looking-at "[0-9]+")
        (progn
          (setq when (- (float-time)
                        (* (string-to-number (match-string 0))
                           quantum)))
          (goto-char (match-end 0)))
      (setq open (char-after))
      (if (setq close (memq open '(?\( ?\[ ?\< ?\{)))
          (setq close (car (last '(?\) ?\] ?\> ?\})
                                 (length close))))
        (setq close open))
      (forward-char)
      (setq end (eshell-find-delimiter open close))
      (unless end
        (error "Malformed %s time modifier `%c'" mod-type mod-char))
      (let* ((file (buffer-substring (point) end))
             (attrs (file-attributes file)))
        (unless attrs
          (error "Cannot stat file `%s'" file))
        (setq when (float-time (nth attr-index attrs))))
      (goto-char (1+ end)))
    `(lambda (file)
       (let ((attrs (file-attributes file)))
         (if attrs
             (,(if (eq qual ?-)
                   '<
                 (if (eq qual ?+)
                     '>
                   '=)) ,when (float-time
                               (nth ,attr-index attrs))))))))

(defun eshell-pred-file-type (type)
  "Return a test which tests that the file is of a certain TYPE.
TYPE must be a character, and should be one of the possible options
that 'ls -l' will show in the first column of its display. "
  (when (eq type ?%)
    (setq type (char-after))
    (if (memq type '(?b ?c))
        (forward-char)
      (setq type ?%)))
  `(lambda (file)
     (let ((attrs (eshell-file-attributes (directory-file-name file))))
       (if attrs
           (memq (aref (nth 8 attrs) 0)
                 ,(if (eq type ?%)
                      '(?b ?c)
                    (list 'quote (list type))))))))

(defsubst eshell-pred-file-mode (mode)
  "Return a test which tests that MODE pertains to the file."
  `(lambda (file)
     (let ((modes (file-modes file)))
       (if modes
           (logand ,mode modes)))))

(defun eshell-pred-file-links ()
  "Return a predicate to test whether a file has a given number of links."
  (let (qual amount)
    (when (memq (char-after) '(?- ?+))
      (setq qual (char-after))
      (forward-char))
    (unless (looking-at "[0-9]+")
      (error "Invalid file link count modifier `l'"))
    (setq amount (string-to-number (match-string 0)))
    (goto-char (match-end 0))
    `(lambda (file)
       (let ((attrs (eshell-file-attributes file)))
         (if attrs
             (,(if (eq qual ?-)
                   '<
                 (if (eq qual ?+)
                     '>
                   '=)) (nth 1 attrs) ,amount))))))

(defun eshell-pred-file-size ()
  "Return a predicate to test whether a file is of a given size."
  (let ((quantum 1) qual amount)
    (when (memq (downcase (char-after)) '(?k ?m ?p))
      (setq qual (downcase (char-after)))
      (cond
       ((eq qual ?k)
        (setq quantum 1024))
       ((eq qual ?m)
        (setq quantum (* 1024 1024)))
       ((eq qual ?p)
        (setq quantum 512)))
      (forward-char))
    (when (memq (char-after) '(?- ?+))
      (setq qual (char-after))
      (forward-char))
    (unless (looking-at "[0-9]+")
      (error "Invalid file size modifier `L'"))
    (setq amount (* (string-to-number (match-string 0)) quantum))
    (goto-char (match-end 0))
    `(lambda (file)
       (let ((attrs (eshell-file-attributes file)))
         (if attrs
             (,(if (eq qual ?-)
                   '<
                 (if (eq qual ?+)
                     '>
                   '=)) (nth 7 attrs) ,amount))))))

(defun eshell-pred-substitute (&optional repeat)
  "Return a modifier function that will substitute matches."
  (let ((delim (char-after))
        match replace end)
    (forward-char)
    (setq end (eshell-find-delimiter delim delim nil nil t)
          match (buffer-substring-no-properties (point) end))
    (goto-char (1+ end))
    (setq end (eshell-find-delimiter delim delim nil nil t)
          replace (buffer-substring-no-properties (point) end))
    (goto-char (1+ end))
    (if repeat
        `(lambda (lst)
           (mapcar
            (function
             (lambda (str)
               (let ((i 0))
                 (while (setq i (string-match ,match str i))
                   (setq str (replace-match ,replace t nil str))))
               str)) lst))
      `(lambda (lst)
         (mapcar
          (function
           (lambda (str)
             (if (string-match ,match str)
                 (setq str (replace-match ,replace t nil str)))
             str)) lst)))))

(defun eshell-include-members (&optional invert-p)
  "Include only lisp members matching a regexp."
  (let ((delim (char-after))
        regexp end)
    (forward-char)
    (setq end (eshell-find-delimiter delim delim nil nil t)
          regexp (buffer-substring-no-properties (point) end))
    (goto-char (1+ end))
    `(lambda (lst)
       (eshell-winnow-list
        lst nil '((lambda (elem)
                    ,(if invert-p
                         `(not (string-match ,regexp elem))
                       `(string-match ,regexp elem))))))))

(defun eshell-join-members ()
  "Return a modifier function that join matches."
  (let ((delim (char-after))
        str end)
    (if (not (memq delim '(?' ?/)))
        (setq delim " ")
      (forward-char)
      (setq end (eshell-find-delimiter delim delim nil nil t)
            str (buffer-substring-no-properties (point) end))
      (goto-char (1+ end)))
    `(lambda (lst)
       (mapconcat 'identity lst ,str))))

(defun eshell-split-members ()
  "Return a modifier function that splits members."
  (let ((delim (char-after))
        sep end)
    (when (memq delim '(?' ?/))
      (forward-char)
      (setq end (eshell-find-delimiter delim delim nil nil t)
            sep (buffer-substring-no-properties (point) end))
      (goto-char (1+ end)))
    `(lambda (lst)
       (mapcar
        (function
         (lambda (str)
           (split-string str ,sep))) lst))))

(provide 'em-pred)

(require 'esh-util)
(eval-when-compile (require 'eshell))

;;;###autoload
(progn
(defgroup eshell-glob nil
  "This module provides extended globbing syntax, similar what is used
by zsh for filename generation."
  :tag "Extended filename globbing"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-glob-load-hook nil
  "A list of functions to run when `eshell-glob' is loaded."
  :version "24.1"                       ; removed eshell-glob-initialize
  :type 'hook
  :group 'eshell-glob)

(defcustom eshell-glob-include-dot-files nil
  "If non-nil, glob patterns will match files beginning with a dot."
  :type 'boolean
  :group 'eshell-glob)

(defcustom eshell-glob-include-dot-dot t
  "If non-nil, glob patterns that match dots will match . and .."
  :type 'boolean
  :group 'eshell-glob)

(defcustom eshell-glob-case-insensitive (eshell-under-windows-p)
  "If non-nil, glob pattern matching will ignore case."
  :type 'boolean
  :group 'eshell-glob)

(defcustom eshell-glob-show-progress nil
  "If non-nil, display progress messages during a recursive glob.
This option slows down recursive glob processing by quite a bit."
  :type 'boolean
  :group 'eshell-glob)

(defcustom eshell-error-if-no-glob nil
  "If non-nil, it is an error for a glob pattern not to match.
 This mimics the behavior of zsh if non-nil, but bash if nil."
  :type 'boolean
  :group 'eshell-glob)

(defcustom eshell-glob-chars-list '(?\] ?\[ ?* ?? ?~ ?\( ?\) ?| ?# ?^)
  "List of additional characters used in extended globbing."
  :type '(repeat character)
  :group 'eshell-glob)

(defcustom eshell-glob-translate-alist
  '((?\] . "]")
    (?\[ . "[")
    (?^  . "^")
    (??  . ".")
    (?*  . ".*")
    (?~  . "~")
    (?\( . "\\(")
    (?\) . "\\)")
    (?\| . "\\|")
    (?#  . (lambda (str pos)
             (if (and (< (1+ pos) (length str))
                      (memq (aref str (1+ pos)) '(?* ?# ?+ ??)))
                 (cons (if (eq (aref str (1+ pos)) ??)
                           "?"
                         (if (eq (aref str (1+ pos)) ?*)
                             "*" "+")) (+ pos 2))
               (cons "*" (1+ pos))))))
  "An alist for translation of extended globbing characters."
  :type '(alist :key-type character
                :value-type (choice string function))
  :group 'eshell-glob)

;;; Functions:

(defun eshell-glob-initialize ()
  "Initialize the extended globbing code."
  ;; it's important that `eshell-glob-chars-list' come first
  (when (boundp 'eshell-special-chars-outside-quoting)
    (set (make-local-variable 'eshell-special-chars-outside-quoting)
         (append eshell-glob-chars-list eshell-special-chars-outside-quoting)))
  (add-hook 'eshell-parse-argument-hook 'eshell-parse-glob-chars t t)
  (add-hook 'eshell-pre-rewrite-command-hook
            'eshell-no-command-globbing nil t))

(defun eshell-no-command-globbing (terms)
  "Don't glob the command argument.  Reflect this by modifying TERMS."
  (ignore
   (when (and (listp (car terms))
              (eq (caar terms) 'eshell-extended-glob))
     (setcar terms (cadr (car terms))))))

(defun eshell-add-glob-modifier ()
  "Add `eshell-extended-glob' to the argument modifier list."
  (when (memq 'expand-file-name eshell-current-modifiers)
    (setq eshell-current-modifiers
          (delq 'expand-file-name eshell-current-modifiers))
    ;; if this is a glob pattern than needs to be expanded, then it
    ;; will need to expand each member of the resulting glob list
    (add-to-list 'eshell-current-modifiers
                 (lambda (list)
                   (if (listp list)
                       (mapcar 'expand-file-name list)
                     (expand-file-name list)))))
  (add-to-list 'eshell-current-modifiers 'eshell-extended-glob))

(defun eshell-parse-glob-chars ()
  "Parse a globbing delimiter.
The character is not advanced for ordinary globbing characters, so
that other function may have a chance to override the globbing
interpretation."
  (when (memq (char-after) eshell-glob-chars-list)
    (if (not (memq (char-after) '(?\( ?\[)))
        (ignore (eshell-add-glob-modifier))
      (let ((here (point)))
        (forward-char)
        (let* ((delim (char-before))
               (end (eshell-find-delimiter
                     delim (if (eq delim ?\[) ?\] ?\)))))
          (if (not end)
              (throw 'eshell-incomplete delim)
            (if (and (eshell-using-module 'eshell-pred)
                     (eshell-arg-delimiter (1+ end)))
                (ignore (goto-char here))
              (eshell-add-glob-modifier)
              (prog1
                  (buffer-substring-no-properties (1- (point)) (1+ end))
                (goto-char (1+ end))))))))))

(defvar eshell-glob-chars-regexp nil)
(defvar eshell-glob-matches)
(defvar message-shown)

(defun eshell-glob-regexp (pattern)
  "Convert glob-pattern PATTERN to a regular expression.
The basic syntax is:

  glob  regexp   meaning
  ----  ------   -------
  ?      .       matches any single character
  *      .*      matches any group of characters (or none)
  #      *       matches zero or more occurrences of preceding
  ##     +       matches one or more occurrences of preceding
  (x)    \(x\)   makes 'x' a regular expression group
  |      \|      boolean OR within an expression group
  [a-b]  [a-b]   matches a character or range
  [^a]   [^a]    excludes a character or range

If any characters in PATTERN have the text property `eshell-escaped'
set to true, then these characters will match themselves in the
resulting regular expression."
  (let ((matched-in-pattern 0)          ; How much of PATTERN handled
        regexp)
    (while (string-match
            (or eshell-glob-chars-regexp
                (set (make-local-variable 'eshell-glob-chars-regexp)
                     (format "[%s]+" (apply 'string eshell-glob-chars-list))))
            pattern matched-in-pattern)
      (let* ((op-begin (match-beginning 0))
             (op-char (aref pattern op-begin)))
        (setq regexp
              (concat regexp
                      (regexp-quote
                       (substring pattern matched-in-pattern op-begin))))
        (if (get-text-property op-begin 'escaped pattern)
            (setq regexp (concat regexp
                                 (regexp-quote (char-to-string op-char)))
                  matched-in-pattern (1+ op-begin))
          (let ((xlat (assq op-char eshell-glob-translate-alist)))
            (if (not xlat)
                (error "Unrecognized globbing character '%c'" op-char)
              (if (stringp (cdr xlat))
                  (setq regexp (concat regexp (cdr xlat))
                        matched-in-pattern (1+ op-begin))
                (let ((result (funcall (cdr xlat) pattern op-begin)))
                  (setq regexp (concat regexp (car result))
                        matched-in-pattern (cdr result)))))))))
    (concat "\\`"
            regexp
            (regexp-quote (substring pattern matched-in-pattern))
            "\\'")))

(defvar ange-cache)                     ; XEmacs?  See esh-util

(defun eshell-extended-glob (glob)
  "Return a list of files generated from GLOB, perhaps looking for DIRS-ONLY.
This function almost fully supports zsh style filename generation
syntax.  Things that are not supported are:

   ^foo        for matching everything but foo
   (foo~bar)   tilde within a parenthesis group
   foo<1-10>   numeric ranges
   foo~x(a|b)  (a|b) will be interpreted as a predicate/modifier list

Mainly they are not supported because file matching is done with Emacs
regular expressions, and these cannot support the above constructs.

If this routine fails, it returns nil.  Otherwise, it returns a list
the form:

   (INCLUDE-REGEXP EXCLUDE-REGEXP (PRED-FUNC-LIST) (MOD-FUNC-LIST))"
  (let ((paths (eshell-split-path glob))
        eshell-glob-matches message-shown ange-cache)
    (unwind-protect
        (if (and (cdr paths)
                 (file-name-absolute-p (car paths)))
            (eshell-glob-entries (file-name-as-directory (car paths))
                                 (cdr paths))
          (eshell-glob-entries (file-name-as-directory ".") paths))
      (if message-shown
          (message nil)))
    (or (and eshell-glob-matches (sort eshell-glob-matches #'string<))
        (if eshell-error-if-no-glob
            (error "No matches found: %s" glob)
          glob))))

;; FIXME does this really need to abuse eshell-glob-matches, message-shown?
(defun eshell-glob-entries (path globs &optional recurse-p)
  "Glob the entries in PATHS, possibly recursing if RECURSE-P is non-nil."
  (let* ((entries (ignore-errors
                    (file-name-all-completions "" path)))
         (case-fold-search eshell-glob-case-insensitive)
         (glob (car globs))
         (len (length glob))
         dirs rdirs
         incl excl
         name isdir pathname)
    (while (cond
            ((and (= len 3) (equal glob "**/"))
             (setq recurse-p 2
                   globs (cdr globs)
                   glob (car globs)
                   len (length glob)))
            ((and (= len 4) (equal glob "***/"))
             (setq recurse-p 3
                   globs (cdr globs)
                   glob (car globs)
                   len (length glob)))))
    (if (and recurse-p (not glob))
        (error "'**' cannot end a globbing pattern"))
    (let ((index 1))
      (setq incl glob)
      (while (and (eq incl glob)
                  (setq index (string-match "~" glob index)))
        (if (or (get-text-property index 'escaped glob)
                (or (= (1+ index) len)))
            (setq index (1+ index))
          (setq incl (substring glob 0 index)
                excl (substring glob (1+ index))))))
    ;; can't use `directory-file-name' because it strips away text
    ;; properties in the string
    (let ((len (1- (length incl))))
      (if (eq (aref incl len) ?/)
          (setq incl (substring incl 0 len)))
      (when excl
        (setq len (1- (length excl)))
        (if (eq (aref excl len) ?/)
            (setq excl (substring excl 0 len)))))
    (setq incl (eshell-glob-regexp incl)
          excl (and excl (eshell-glob-regexp excl)))
    (if (or eshell-glob-include-dot-files
            (eq (aref glob 0) ?.))
        (unless (or eshell-glob-include-dot-dot
                    (cdr globs))
          (setq excl (if excl
                         (concat "\\(\\`\\.\\.?\\'\\|" excl "\\)")
                       "\\`\\.\\.?\\'")))
      (setq excl (if excl
                     (concat "\\(\\`\\.\\|" excl "\\)")
                   "\\`\\.")))
    (when (and recurse-p eshell-glob-show-progress)
      (message "Building file list...%d so far: %s"
               (length eshell-glob-matches) path)
      (setq message-shown t))
    (if (equal path "./") (setq path ""))
    (while entries
      (setq name (car entries)
            len (length name)
            isdir (eq (aref name (1- len)) ?/))
      (if (let ((fname (directory-file-name name)))
            (and (not (and excl (string-match excl fname)))
                 (string-match incl fname)))
          (if (cdr globs)
              (if isdir
                  (setq dirs (cons (concat path name) dirs)))
            (setq eshell-glob-matches
                  (cons (concat path name) eshell-glob-matches))))
      (if (and recurse-p isdir
               (or (> len 3)
                   (not (or (and (= len 2) (equal name "./"))
                            (and (= len 3) (equal name "../")))))
               (setq pathname (concat path name))
               (not (and (= recurse-p 2)
                         (file-symlink-p
                          (directory-file-name pathname)))))
          (setq rdirs (cons pathname rdirs)))
      (setq entries (cdr entries)))
    (setq dirs (nreverse dirs)
          rdirs (nreverse rdirs))
    (while dirs
      (eshell-glob-entries (car dirs) (cdr globs))
      (setq dirs (cdr dirs)))
    (while rdirs
      (eshell-glob-entries (car rdirs) globs recurse-p)
      (setq rdirs (cdr rdirs)))))

(provide 'em-glob)

(eval-when-compile (require 'cl-lib))

(require 'ring)
(require 'esh-opt)
(require 'em-pred)
(require 'eshell)

;;;###autoload
(progn
(defgroup eshell-hist nil
  "This module provides command history management."
  :tag "History list management"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-hist-load-hook nil
  "A list of functions to call when loading `eshell-hist'."
  :version "24.1"                       ; removed eshell-hist-initialize
  :type 'hook
  :group 'eshell-hist)

(defcustom eshell-hist-unload-hook
  (list
   (function
    (lambda ()
      (remove-hook 'kill-emacs-hook 'eshell-save-some-history))))
  "A hook that gets run when `eshell-hist' is unloaded."
  :type 'hook
  :group 'eshell-hist)

(defcustom eshell-history-file-name
  (expand-file-name "history" eshell-directory-name)
  "If non-nil, name of the file to read/write input history.
See also `eshell-read-history' and `eshell-write-history'.
If it is nil, Eshell will use the value of HISTFILE."
  :type '(choice (const :tag "Use HISTFILE" nil)
                 file)
  :group 'eshell-hist)

(defcustom eshell-history-size 128
  "Size of the input history ring.  If nil, use envvar HISTSIZE."
  :type '(choice (const :tag "Use HISTSIZE" nil)
                 integer)
  :group 'eshell-hist)

(defcustom eshell-hist-ignoredups nil
  "If non-nil, don't add input matching the last on the input ring.
This mirrors the optional behavior of bash."
  :type 'boolean
  :group 'eshell-hist)

(defcustom eshell-save-history-on-exit t
  "Determine if history should be automatically saved.
History is always preserved after sanely exiting an Eshell buffer.
However, when Emacs is being shut down, this variable determines
whether to prompt the user.
If set to nil, it means never save history on termination of Emacs.
If set to `ask', ask if any Eshell buffers are open at exit time.
If set to t, history will always be saved, silently."
  :type '(choice (const :tag "Never" nil)
                 (const :tag "Ask" ask)
                 (const :tag "Always save" t))
  :group 'eshell-hist)

(defcustom eshell-input-filter
  (function
   (lambda (str)
     (not (string-match "\\`\\s-*\\'" str))))
  "Predicate for filtering additions to input history.
Takes one argument, the input.  If non-nil, the input may be saved on
the input history list.  Default is to save anything that isn't all
whitespace."
  :type 'function
  :group 'eshell-hist)

(put 'eshell-input-filter 'risky-local-variable t)

(defcustom eshell-hist-match-partial t
  "If non-nil, movement through history is constrained by current input.
Otherwise, typing <M-p> and <M-n> will always go to the next history
element, regardless of any text on the command line.  In that case,
<C-c M-r> and <C-c M-s> still offer that functionality."
  :type 'boolean
  :group 'eshell-hist)

(defcustom eshell-hist-move-to-end t
  "If non-nil, move to the end of the buffer before cycling history."
  :type 'boolean
  :group 'eshell-hist)

(defcustom eshell-hist-event-designator
  "^!\\(!\\|-?[0-9]+\\|\\??[^:^$%*?]+\\??\\|#\\)"
  "The regexp used to identifier history event designators."
  :type 'regexp
  :group 'eshell-hist)

(defcustom eshell-hist-word-designator
  "^:?\\([0-9]+\\|[$^%*]\\)?\\(\\*\\|-[0-9]*\\|[$^%*]\\)?"
  "The regexp used to identify history word designators."
  :type 'regexp
  :group 'eshell-hist)

(defcustom eshell-hist-modifier
  "^\\(:\\([hretpqx&g]\\|s/\\([^/]*\\)/\\([^/]*\\)/\\)\\)*"
  "The regexp used to identity history modifiers."
  :type 'regexp
  :group 'eshell-hist)

(defcustom eshell-hist-rebind-keys-alist
  '(([(control ?p)]   . eshell-previous-input)
    ([(control ?n)]   . eshell-next-input)
    ([(control up)]   . eshell-previous-input)
    ([(control down)] . eshell-next-input)
    ([(control ?r)]   . eshell-isearch-backward)
    ([(control ?s)]   . eshell-isearch-forward)
    ([(meta ?r)]      . eshell-previous-matching-input)
    ([(meta ?s)]      . eshell-next-matching-input)
    ([(meta ?p)]      . eshell-previous-matching-input-from-input)
    ([(meta ?n)]      . eshell-next-matching-input-from-input)
    ([up]             . eshell-previous-matching-input-from-input)
    ([down]           . eshell-next-matching-input-from-input))
  "History keys to bind differently if point is in input text."
  :type '(repeat (cons (vector :tag "Keys to bind"
                               (repeat :inline t sexp))
                       (function :tag "Command")))
  :group 'eshell-hist)

;;; Internal Variables:

(defvar eshell-history-ring nil)
(defvar eshell-history-index nil)
(defvar eshell-matching-input-from-input-string "")
(defvar eshell-save-history-index nil)

(defvar eshell-isearch-map
  (let ((map (copy-keymap isearch-mode-map)))
    (define-key map [(control ?m)] 'eshell-isearch-return)
    (define-key map [return] 'eshell-isearch-return)
    (define-key map [(control ?r)] 'eshell-isearch-repeat-backward)
    (define-key map [(control ?s)] 'eshell-isearch-repeat-forward)
    (define-key map [(control ?g)] 'eshell-isearch-abort)
    (define-key map [backspace] 'eshell-isearch-delete-char)
    (define-key map [delete] 'eshell-isearch-delete-char)
    (define-key map "\C-c\C-c" 'eshell-isearch-cancel)
    map)
  "Keymap used in isearch in Eshell.")

(defvar eshell-rebind-keys-alist)

;;; Functions:

(defun eshell-hist-initialize ()
  "Initialize the history management code for one Eshell buffer."
  (add-hook 'eshell-expand-input-functions
            'eshell-expand-history-references nil t)

  (when (eshell-using-module 'eshell-cmpl)
    (add-hook 'pcomplete-try-first-hook
              'eshell-complete-history-reference nil t))

  (if (and (eshell-using-module 'eshell-rebind)
           (not eshell-non-interactive-p))
      (let ((rebind-alist eshell-rebind-keys-alist))
        (make-local-variable 'eshell-rebind-keys-alist)
        (setq eshell-rebind-keys-alist
              (append rebind-alist eshell-hist-rebind-keys-alist))
        (set (make-local-variable 'search-invisible) t)
        (set (make-local-variable 'search-exit-option) t)
        (add-hook 'isearch-mode-hook
                  (function
                   (lambda ()
                     (if (>= (point) eshell-last-output-end)
                         (setq overriding-terminal-local-map
                               eshell-isearch-map)))) nil t)
        (add-hook 'isearch-mode-end-hook
                  (function
                   (lambda ()
                     (setq overriding-terminal-local-map nil))) nil t))
    (define-key eshell-mode-map [up] 'eshell-previous-matching-input-from-input)
    (define-key eshell-mode-map [down] 'eshell-next-matching-input-from-input)
    (define-key eshell-mode-map [(control up)] 'eshell-previous-input)
    (define-key eshell-mode-map [(control down)] 'eshell-next-input)
    (define-key eshell-mode-map [(meta ?r)] 'eshell-previous-matching-input)
    (define-key eshell-mode-map [(meta ?s)] 'eshell-next-matching-input)
    (define-key eshell-command-map [(meta ?r)]
      'eshell-previous-matching-input-from-input)
    (define-key eshell-command-map [(meta ?s)]
      'eshell-next-matching-input-from-input)
    (if eshell-hist-match-partial
        (progn
          (define-key eshell-mode-map [(meta ?p)]
            'eshell-previous-matching-input-from-input)
          (define-key eshell-mode-map [(meta ?n)]
            'eshell-next-matching-input-from-input)
          (define-key eshell-command-map [(meta ?p)] 'eshell-previous-input)
          (define-key eshell-command-map [(meta ?n)] 'eshell-next-input))
      (define-key eshell-mode-map [(meta ?p)] 'eshell-previous-input)
      (define-key eshell-mode-map [(meta ?n)] 'eshell-next-input)
      (define-key eshell-command-map [(meta ?p)]
        'eshell-previous-matching-input-from-input)
      (define-key eshell-command-map [(meta ?n)]
        'eshell-next-matching-input-from-input)))

  (make-local-variable 'eshell-history-size)
  (or eshell-history-size
      (let ((hsize (getenv "HISTSIZE")))
        (setq eshell-history-size
              (if (and (stringp hsize)
                       (integerp (setq hsize (string-to-number hsize)))
                       (> hsize 0))
                  hsize
                128))))

  (make-local-variable 'eshell-history-file-name)
  (or eshell-history-file-name
      (setq eshell-history-file-name (getenv "HISTFILE")))

  (make-local-variable 'eshell-history-index)
  (make-local-variable 'eshell-save-history-index)

  (if (minibuffer-window-active-p (selected-window))
      (set (make-local-variable 'eshell-save-history-on-exit) nil)
    (set (make-local-variable 'eshell-history-ring) nil)
    (if eshell-history-file-name
        (eshell-read-history nil t))

    (add-hook 'eshell-exit-hook 'eshell-write-history nil t))

  (unless eshell-history-ring
    (setq eshell-history-ring (make-ring eshell-history-size)))

  (add-hook 'eshell-exit-hook 'eshell-write-history nil t)

  (add-hook 'kill-emacs-hook 'eshell-save-some-history)

  (make-local-variable 'eshell-input-filter-functions)
  (add-hook 'eshell-input-filter-functions 'eshell-add-to-history nil t)

  (define-key eshell-command-map [(control ?l)] 'eshell-list-history)
  (define-key eshell-command-map [(control ?x)] 'eshell-get-next-from-history))

(defun eshell-save-some-history ()
  "Save the history for any open Eshell buffers."
  (dolist (buf (buffer-list))
    (if (buffer-live-p buf)
        (with-current-buffer buf
          (if (and eshell-mode
                   eshell-history-file-name
                   eshell-save-history-on-exit
                   (or (eq eshell-save-history-on-exit t)
                       (y-or-n-p
                        (format "Save input history for Eshell buffer `%s'? "
                                (buffer-name buf)))))
              (eshell-write-history))))))

(defun eshell/history (&rest args)
  "List in help buffer the buffer's input history."
  (eshell-init-print-buffer)
  (eshell-eval-using-options
   "history" args
   '((?r "read" nil read-history
         "read from history file to current history list")
     (?w "write" nil write-history
         "write current history list to history file")
     (?a "append" nil append-history
         "append current history list to history file")
     (?h "help" nil nil "display this usage message")
     :usage "[n] [-rwa [filename]]"
     :post-usage
"When Eshell is started, history is read from `eshell-history-file-name'.
This is also the location where history info will be saved by this command,
unless a different file is specified on the command line.")
   (and (or (not (ring-p eshell-history-ring))
           (ring-empty-p eshell-history-ring))
        (error "No history"))
   (let (length file)
     (when (and args (string-match "^[0-9]+$" (car args)))
       (setq length (min (eshell-convert (car args))
                         (ring-length eshell-history-ring))
             args (cdr args)))
     (and length
          (or read-history write-history append-history)
          (error "history: extra arguments"))
     (when (and args (stringp (car args)))
       (setq file (car args)
             args (cdr args)))
     (cond
      (read-history (eshell-read-history file))
      (write-history (eshell-write-history file))
      (append-history (eshell-write-history file t))
      (t
       (let* ((index (1- (or length (ring-length eshell-history-ring))))
              (ref (- (ring-length eshell-history-ring) index)))
         ;; We have to build up a list ourselves from the ring vector.
         (while (>= index 0)
           (eshell-buffered-print
            (format "%5d  %s\n" ref (eshell-get-history index)))
           (setq index (1- index)
                 ref (1+ ref)))))))
   (eshell-flush)
   nil))

(defun eshell-put-history (input &optional ring at-beginning)
  "Put a new input line into the history ring."
  (unless ring (setq ring eshell-history-ring))
  (if at-beginning
      (ring-insert-at-beginning ring input)
    (ring-insert ring input)))

(defun eshell-get-history (index &optional ring)
  "Get an input line from the history ring."
  (ring-ref (or ring eshell-history-ring) index))

(defun eshell-add-input-to-history (input)
  "Add the string INPUT to the history ring.
Input is entered into the input history ring, if the value of
variable `eshell-input-filter' returns non-nil when called on the
input."
  (if (and (funcall eshell-input-filter input)
           (or (null eshell-hist-ignoredups)
               (not (ring-p eshell-history-ring))
               (ring-empty-p eshell-history-ring)
               (not (string-equal (eshell-get-history 0) input))))
      (eshell-put-history input))
  (setq eshell-save-history-index eshell-history-index)
  (setq eshell-history-index nil))

(defun eshell-add-command-to-history ()
  "Add the command entered at `eshell-command's prompt to the history ring.
The command is added to the input history ring, if the value of
variable `eshell-input-filter' returns non-nil when called on the
command.

This function is supposed to be called from the minibuffer, presumably
as a minibuffer-exit-hook."
  (eshell-add-input-to-history
   (buffer-substring (minibuffer-prompt-end) (point-max))))

(defun eshell-add-to-history ()
  "Add last Eshell command to the history ring.
The command is entered into the input history ring, if the value of
variable `eshell-input-filter' returns non-nil when called on the
command."
  (when (> (1- eshell-last-input-end) eshell-last-input-start)
    (let ((input (buffer-substring eshell-last-input-start
                                   (1- eshell-last-input-end))))
      (eshell-add-input-to-history input))))

(defun eshell-read-history (&optional filename silent)
  "Sets the buffer's `eshell-history-ring' from a history file.
The name of the file is given by the variable
`eshell-history-file-name'.  The history ring is of size
`eshell-history-size', regardless of file size.  If
`eshell-history-file-name' is nil this function does nothing.

If the optional argument SILENT is non-nil, we say nothing about a
failure to read the history file.

This function is useful for major mode commands and mode hooks.

The structure of the history file should be one input command per
line, with the most recent command last.  See also
`eshell-hist-ignoredups' and `eshell-write-history'."
  (let ((file (or filename eshell-history-file-name)))
    (cond
     ((or (null file)
          (equal file ""))
      nil)
     ((not (file-readable-p file))
      (or silent
          (message "Cannot read history file %s" file)))
     (t
      (let* ((count 0)
             (size eshell-history-size)
             (ring (make-ring size))
             (ignore-dups eshell-hist-ignoredups))
        (with-temp-buffer
          (insert-file-contents file)
          ;; Save restriction in case file is already visited...
          ;; Watch for those date stamps in history files!
          (goto-char (point-max))
          (while (and (< count size)
                      (re-search-backward "^[ \t]*\\([^#\n].*\\)[ \t]*$"
                                          nil t))
            (let ((history (match-string 1)))
              (if (or (null ignore-dups)
                      (ring-empty-p ring)
                      (not (string-equal (ring-ref ring 0) history)))
                  (ring-insert-at-beginning
                   ring (subst-char-in-string ?\177 ?\n history))))
            (setq count (1+ count))))
        (setq eshell-history-ring ring
              eshell-history-index nil))))))

(defun eshell-write-history (&optional filename append)
  "Writes the buffer's `eshell-history-ring' to a history file.
The name of the file is given by the variable
`eshell-history-file-name'.  The original contents of the file are
lost if `eshell-history-ring' is not empty.  If
`eshell-history-file-name' is nil this function does nothing.

Useful within process sentinels.

See also `eshell-read-history'."
  (let ((file (or filename eshell-history-file-name)))
    (cond
     ((or (null file)
          (equal file "")
          (null eshell-history-ring)
          (ring-empty-p eshell-history-ring))
      nil)
     ((not (file-writable-p file))
      (message "Cannot write history file %s" file))
     (t
      (let* ((ring eshell-history-ring)
             (index (ring-length ring)))
        ;; Write it all out into a buffer first.  Much faster, but
        ;; messier, than writing it one line at a time.
        (with-temp-buffer
          (while (> index 0)
            (setq index (1- index))
            (let ((start (point)))
              (insert (ring-ref ring index) ?\n)
              (subst-char-in-region start (1- (point)) ?\n ?\177)))
          (eshell-with-private-file-modes
           (write-region (point-min) (point-max) file append
                         'no-message))))))))

(defun eshell-list-history ()
  "List in help buffer the buffer's input history."
  (interactive)
  (let (prefix prelen)
    (save-excursion
      (if (re-search-backward "!\\(.+\\)" (line-beginning-position) t)
          (setq prefix (match-string 1)
                prelen (length prefix))))
    (if (or (not (ring-p eshell-history-ring))
            (ring-empty-p eshell-history-ring))
        (message "No history")
      (let ((history nil)
            (history-buffer " *Input History*")
            (index (1- (ring-length eshell-history-ring)))
            (conf (current-window-configuration)))
        ;; We have to build up a list ourselves from the ring vector.
        (while (>= index 0)
          (let ((hist (eshell-get-history index)))
            (if (or (not prefix)
                    (and (>= (length hist) prelen)
                         (string= (substring hist 0 prelen) prefix)))
                (setq history (cons hist history))))
          (setq index (1- index)))
        ;; Change "completion" to "history reference"
        ;; to make the display accurate.
        (with-output-to-temp-buffer history-buffer
          (display-completion-list
           (completion-hilit-commonality history (length prefix)))
          (set-buffer history-buffer)
          (forward-line 3)
          (while (search-backward "completion" nil 'move)
            (replace-match "history reference")))
        (eshell-redisplay)
        (message "Hit space to flush")
        (let ((ch (read-event)))
          (if (eq ch ?\ )
              (set-window-configuration conf)
            (setq unread-command-events (list ch))))))))

(defun eshell-hist-word-reference (ref)
  "Return the word designator index referred to by REF."
  (cond
   ((string-match "^[0-9]+$" ref)
    (string-to-number ref))
   ((string= "^" ref) 1)
   ((string= "$" ref) nil)
   ((string= "%" ref)
    (error "`%%' history word designator not yet implemented"))))

(defun eshell-hist-parse-arguments (&optional b e)
  "Parse current command arguments in a history-code-friendly way."
  (let ((end (or e (point)))
        (begin (or b (save-excursion (eshell-bol) (point))))
        (posb (list t))
        (pose (list t))
        (textargs (list t))
        hist args)
    (unless (catch 'eshell-incomplete
              (ignore
               (setq args (eshell-parse-arguments begin end))))
      (save-excursion
        (goto-char begin)
        (while (< (point) end)
          (if (get-text-property (point) 'arg-begin)
              (nconc posb (list (point))))
          (if (get-text-property (point) 'arg-end)
              (nconc pose
                     (list (if (= (1+ (point)) end)
                               (1+ (point))
                             (point)))))
          (forward-char))
        (setq posb (cdr posb)
              pose (cdr pose))
        (cl-assert (= (length posb) (length args)))
        (cl-assert (<= (length posb) (length pose))))
      (setq hist (buffer-substring-no-properties begin end))
      (let ((b posb) (e pose))
        (while b
          (nconc textargs
                 (list (substring hist (- (car b) begin)
                                  (- (car e) begin))))
          (setq b (cdr b)
                e (cdr e))))
      (setq textargs (cdr textargs))
      (cl-assert (= (length textargs) (length args)))
      (list textargs posb pose))))

(defun eshell-expand-history-references (beg end)
  "Parse and expand any history references in current input."
  (let ((result (eshell-hist-parse-arguments beg end)))
    (when result
      (let ((textargs (nreverse (nth 0 result)))
            (posb (nreverse (nth 1 result)))
            (pose (nreverse (nth 2 result))))
        (save-excursion
          (while textargs
            (let ((str (eshell-history-reference (car textargs))))
              (unless (eq str (car textargs))
                (goto-char (car posb))
                (insert-and-inherit str)
                (delete-char (- (car pose) (car posb)))))
            (setq textargs (cdr textargs)
                  posb (cdr posb)
                  pose (cdr pose))))))))

(defvar pcomplete-stub)
(defvar pcomplete-last-completion-raw)
(declare-function pcomplete-actual-arg "pcomplete")

(defun eshell-complete-history-reference ()
  "Complete a history reference, by completing the event designator."
  (let ((arg (pcomplete-actual-arg)))
    (when (string-match "\\`![^:^$*%]*\\'" arg)
      (setq pcomplete-stub (substring arg 1)
            pcomplete-last-completion-raw t)
      (throw 'pcomplete-completions
             (let ((history nil)
                   (index (1- (ring-length eshell-history-ring)))
                   (stublen (length pcomplete-stub)))
               ;; We have to build up a list ourselves from the ring
               ;; vector.
               (while (>= index 0)
                 (let ((hist (eshell-get-history index)))
                   (if (and (>= (length hist) stublen)
                            (string= (substring hist 0 stublen)
                                     pcomplete-stub)
                            (string-match "^\\([^:^$*% \t\n]+\\)" hist))
                       (setq history (cons (match-string 1 hist)
                                           history))))
                 (setq index (1- index)))
               (let ((fhist (list t)))
                 ;; uniquify the list, but preserve the order
                 (while history
                   (unless (member (car history) fhist)
                     (nconc fhist (list (car history))))
                   (setq history (cdr history)))
                 (cdr fhist)))))))

(defun eshell-history-reference (reference)
  "Expand directory stack REFERENCE.
The syntax used here was taken from the Bash info manual.
Returns the resultant reference, or the same string REFERENCE if none
matched."
  ;; `^string1^string2^'
  ;;      Quick Substitution.  Repeat the last command, replacing
  ;;      STRING1 with STRING2.  Equivalent to `!!:s/string1/string2/'
  (if (and (eshell-using-module 'eshell-pred)
           (string-match "\\^\\([^^]+\\)\\^\\([^^]+\\)\\^?\\s-*$"
                         reference))
      (setq reference (format "!!:s/%s/%s/"
                              (match-string 1 reference)
                              (match-string 2 reference))))
  ;; `!'
  ;;      Start a history substitution, except when followed by a
  ;;      space, tab, the end of the line, = or (.
  (if (not (string-match "^![^ \t\n=\(]" reference))
      reference
    (setq eshell-history-index nil)
    (let ((event (eshell-hist-parse-event-designator reference)))
      (unless event
        (error "Could not find history event `%s'" reference))
      (setq eshell-history-index (car event)
            reference (substring reference (cdr event))
            event (eshell-get-history eshell-history-index))
      (if (not (string-match "^[:^$*%]" reference))
          event
        (let ((word (eshell-hist-parse-word-designator
                     event reference)))
          (unless word
            (error "Unable to honor word designator `%s'" reference))
          (unless (string-match "^[:^$*%][[$^*%0-9-]" reference)
            (setcdr word 0))
          (setq event (car word)
                reference (substring reference (cdr word)))
          (if (not (and (eshell-using-module 'eshell-pred)
                        (string-match "^:" reference)))
              event
            (eshell-hist-parse-modifier event reference)))))))

(defun eshell-hist-parse-event-designator (reference)
  "Parse a history event designator beginning in REFERENCE."
  (let* ((index (string-match eshell-hist-event-designator reference))
         (end (and index (match-end 0))))
    (unless index
      (error "Invalid history event designator `%s'" reference))
    (let* ((event (match-string 1 reference))
           (pos
            (cond
             ((string= event "!") (ring-length eshell-history-ring))
             ((string= event "#") (error "!# not yet implemented"))
             ((string-match "^-?[0-9]+$" event)
              (let ((num (string-to-number event)))
                (if (>= num 0)
                    (- (ring-length eshell-history-ring) num)
                  (1- (abs num)))))
             ((string-match "^\\(\\??\\)\\([^?]+\\)\\??$" event)
              (let ((pref (if (> (length (match-string 1 event)) 0)
                              "" "^"))
                    (str (match-string 2 event)))
                (save-match-data
                  (eshell-previous-matching-input-string-position
                   (concat pref (regexp-quote str)) 1))))
             (t
              (error "Failed to parse event designator `%s'" event)))))
      (and pos (cons pos end)))))

(defun eshell-hist-parse-word-designator (hist reference)
  "Parse a history word designator beginning for HIST in REFERENCE."
  (let* ((index (string-match eshell-hist-word-designator reference))
         (end (and index (match-end 0))))
    (unless (memq (aref reference 0) '(?: ?^ ?$ ?* ?%))
      (error "Invalid history word designator `%s'" reference))
    (let ((nth (match-string 1 reference))
          (mth (match-string 2 reference))
          (here (point))
          textargs)
      (insert hist)
      (setq textargs (car (eshell-hist-parse-arguments here (point))))
      (delete-region here (point))
      (if (string= nth "*")
          (if mth
              (error "Invalid history word designator `%s'"
                     reference)
            (setq nth 1 mth "-$")))
      (if (not mth)
          (if nth
              (setq mth nth)
            (setq nth 0 mth "$"))
        (if (string= mth "-")
            (setq mth (- (length textargs) 2))
          (if (string= mth "*")
              (setq mth "$")
            (if (not (and (> (length mth) 1)
                          (eq (aref mth 0) ?-)))
                (error "Invalid history word designator `%s'"
                       reference)
              (setq mth (substring mth 1))))))
      (unless (numberp nth)
        (setq nth (eshell-hist-word-reference nth)))
      (unless (numberp mth)
        (setq mth (eshell-hist-word-reference mth)))
      (cons (mapconcat 'identity (eshell-sublist textargs nth mth) "")
            end))))

(defun eshell-hist-parse-modifier (hist reference)
  "Parse a history modifier beginning for HIST in REFERENCE."
  (let ((here (point)))
    (insert reference)
    (prog1
        (save-restriction
          (narrow-to-region here (point))
          (goto-char (point-min))
          (let ((modifiers (cdr (eshell-parse-modifiers))))
            (dolist (mod modifiers)
              (setq hist (funcall mod hist)))
            hist))
      (delete-region here (point)))))

(defun eshell-get-next-from-history ()
  "After fetching a line from input history, this fetches the next.
In other words, this recalls the input line after the line you
recalled last.  You can use this to repeat a sequence of input lines."
  (interactive)
  (if eshell-save-history-index
      (progn
        (setq eshell-history-index (1+ eshell-save-history-index))
        (eshell-next-input 1))
    (message "No previous history command")))

(defun eshell-search-arg (arg)
  ;; First make sure there is a ring and that we are after the process
  ;; mark
  (if (and eshell-hist-move-to-end
           (< (point) eshell-last-output-end))
      (goto-char eshell-last-output-end))
  (cond ((or (null eshell-history-ring)
             (ring-empty-p eshell-history-ring))
         (error "Empty input ring"))
        ((zerop arg)
         ;; arg of zero resets search from beginning, and uses arg of
         ;; 1
         (setq eshell-history-index nil)
         1)
        (t
         arg)))

(defun eshell-search-start (arg)
  "Index to start a directional search, starting at `eshell-history-index'."
  (if eshell-history-index
      ;; If a search is running, offset by 1 in direction of arg
      (mod (+ eshell-history-index (if (> arg 0) 1 -1))
           (ring-length eshell-history-ring))
    ;; For a new search, start from beginning or end, as appropriate
    (if (>= arg 0)
        0                               ; First elt for forward search
      ;; Last elt for backward search
      (1- (ring-length eshell-history-ring)))))

(defun eshell-previous-input-string (arg)
  "Return the string ARG places along the input ring.
Moves relative to `eshell-history-index'."
  (eshell-get-history (if eshell-history-index
                          (mod (+ arg eshell-history-index)
                               (ring-length eshell-history-ring))
                        arg)))

(defun eshell-previous-input (arg)
  "Cycle backwards through input history."
  (interactive "*p")
  (eshell-previous-matching-input "." arg))

(defun eshell-next-input (arg)
  "Cycle forwards through input history."
  (interactive "*p")
  (eshell-previous-input (- arg)))

(defun eshell-previous-matching-input-string (regexp arg)
  "Return the string matching REGEXP ARG places along the input ring.
Moves relative to `eshell-history-index'."
  (let* ((pos (eshell-previous-matching-input-string-position regexp arg)))
    (if pos (eshell-get-history pos))))

(defun eshell-previous-matching-input-string-position
  (regexp arg &optional start)
  "Return the index matching REGEXP ARG places along the input ring.
Moves relative to START, or `eshell-history-index'."
  (if (or (not (ring-p eshell-history-ring))
          (ring-empty-p eshell-history-ring))
      (error "No history"))
  (let* ((len (ring-length eshell-history-ring))
         (motion (if (> arg 0) 1 -1))
         (n (mod (- (or start (eshell-search-start arg)) motion) len))
         (tried-each-ring-item nil)
         (case-fold-search (eshell-under-windows-p))
         (prev nil))
    ;; Do the whole search as many times as the argument says.
    (while (and (/= arg 0) (not tried-each-ring-item))
      ;; Step once.
      (setq prev n
            n (mod (+ n motion) len))
      ;; If we haven't reached a match, step some more.
      (while (and (< n len) (not tried-each-ring-item)
                  (not (string-match regexp (eshell-get-history n))))
        (setq n (mod (+ n motion) len)
              ;; If we have gone all the way around in this search.
              tried-each-ring-item (= n prev)))
      (setq arg (if (> arg 0) (1- arg) (1+ arg))))
    ;; Now that we know which ring element to use, if we found it,
    ;; return that.
    (if (string-match regexp (eshell-get-history n))
        n)))

(defun eshell-previous-matching-input (regexp arg)
  "Search backwards through input history for match for REGEXP.
\(Previous history elements are earlier commands.)
With prefix argument N, search for Nth previous match.
If N is negative, find the next or Nth next match."
  (interactive (eshell-regexp-arg "Previous input matching (regexp): "))
  (setq arg (eshell-search-arg arg))
  (if (> eshell-last-output-end (point))
      (error "Point not located after prompt"))
  (let ((pos (eshell-previous-matching-input-string-position regexp arg)))
    ;; Has a match been found?
    (if (null pos)
        (error "Not found")
      (setq eshell-history-index pos)
      (unless (minibuffer-window-active-p (selected-window))
        (message "History item: %d" (- (ring-length eshell-history-ring) pos)))
      ;; Can't use kill-region as it sets this-command
      (delete-region eshell-last-output-end (point))
      (insert-and-inherit (eshell-get-history pos)))))

(defun eshell-next-matching-input (regexp arg)
  "Search forwards through input history for match for REGEXP.
\(Later history elements are more recent commands.)
With prefix argument N, search for Nth following match.
If N is negative, find the previous or Nth previous match."
  (interactive (eshell-regexp-arg "Next input matching (regexp): "))
  (eshell-previous-matching-input regexp (- arg)))

(defun eshell-previous-matching-input-from-input (arg)
  "Search backwards through input history for match for current input.
\(Previous history elements are earlier commands.)
With prefix argument N, search for Nth previous match.
If N is negative, search forwards for the -Nth following match."
  (interactive "p")
  (if (not (memq last-command '(eshell-previous-matching-input-from-input
                                eshell-next-matching-input-from-input)))
      ;; Starting a new search
      (setq eshell-matching-input-from-input-string
            (buffer-substring (save-excursion (eshell-bol) (point))
                              (point))
            eshell-history-index nil))
  (eshell-previous-matching-input
   (concat "^" (regexp-quote eshell-matching-input-from-input-string))
   arg))

(defun eshell-next-matching-input-from-input (arg)
  "Search forwards through input history for match for current input.
\(Following history elements are more recent commands.)
With prefix argument N, search for Nth following match.
If N is negative, search backwards for the -Nth previous match."
  (interactive "p")
  (eshell-previous-matching-input-from-input (- arg)))

(defun eshell-test-imatch ()
  "If isearch match good, put point at the beginning and return non-nil."
  (if (get-text-property (point) 'history)
      (progn (beginning-of-line) t)
    (let ((before (point)))
      (eshell-bol)
      (if (and (not (bolp))
               (<= (point) before))
          t
        (if isearch-forward
            (progn
              (end-of-line)
              (forward-char))
          (beginning-of-line)
          (backward-char))))))

(defun eshell-return-to-prompt ()
  "Once a search string matches, insert it at the end and go there."
  (setq isearch-other-end nil)
  (let ((found (eshell-test-imatch)) before)
    (while (and (not found)
                (setq before
                      (funcall (if isearch-forward
                                   're-search-forward
                                 're-search-backward)
                               isearch-string nil t)))
      (setq found (eshell-test-imatch)))
    (if (not found)
        (progn
          (goto-char eshell-last-output-end)
          (delete-region (point) (point-max)))
      (setq before (point))
      (let ((text (buffer-substring-no-properties
                   (point) (line-end-position)))
            (orig (marker-position eshell-last-output-end)))
        (goto-char eshell-last-output-end)
        (delete-region (point) (point-max))
        (when (and text (> (length text) 0))
          (insert text)
          (put-text-property (1- (point)) (point)
                             'last-search-pos before)
          (set-marker eshell-last-output-end orig)
          (goto-char eshell-last-output-end))))))

(defun eshell-prepare-for-search ()
  "Make sure the old history file is at the beginning of the buffer."
  (unless (get-text-property (point-min) 'history)
    (save-excursion
      (goto-char (point-min))
      (let ((end (copy-marker (point) t)))
        (insert-file-contents eshell-history-file-name)
        (set-text-properties (point-min) end
                             '(history t invisible t))))))

(defun eshell-isearch-backward (&optional invert)
  "Do incremental regexp search backward through past commands."
  (interactive)
  (let ((inhibit-read-only t))
    (eshell-prepare-for-search)
    (goto-char (point-max))
    (set-marker eshell-last-output-end (point))
    (delete-region (point) (point-max)))
  (isearch-mode invert t 'eshell-return-to-prompt))

(defun eshell-isearch-repeat-backward (&optional invert)
  "Do incremental regexp search backward through past commands."
  (interactive)
  (let ((old-pos (get-text-property (1- (point-max))
                                    'last-search-pos)))
    (when old-pos
      (goto-char old-pos)
      (if invert
          (end-of-line)
        (backward-char)))
    (setq isearch-forward invert)
    (isearch-search-and-update)))

(defun eshell-isearch-forward ()
  "Do incremental regexp search backward through past commands."
  (interactive)
  (eshell-isearch-backward t))

(defun eshell-isearch-repeat-forward ()
  "Do incremental regexp search backward through past commands."
  (interactive)
  (eshell-isearch-repeat-backward t))

(defun eshell-isearch-cancel ()
  (interactive)
  (goto-char eshell-last-output-end)
  (delete-region (point) (point-max))
  (call-interactively 'isearch-cancel))

(defun eshell-isearch-abort ()
  (interactive)
  (goto-char eshell-last-output-end)
  (delete-region (point) (point-max))
  (call-interactively 'isearch-abort))

(defun eshell-isearch-delete-char ()
  (interactive)
  (save-excursion
  (isearch-delete-char)))

(defun eshell-isearch-return ()
  (interactive)
  (isearch-done)
  (eshell-send-input))

(provide 'em-hist)

(require 'cl-lib)
(require 'esh-util)
(require 'esh-opt)
(eval-when-compile (require 'eshell))

;;;###autoload
(progn
(defgroup eshell-ls nil
  "This module implements the \"ls\" utility fully in Lisp.  If it is
passed any unrecognized command switches, it will revert to the
operating system's version.  This version of \"ls\" uses text
properties to colorize its output based on the setting of
`eshell-ls-use-colors'."
  :tag "Implementation of `ls' in Lisp"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-ls-date-format "%Y-%m-%d"
  "How to display time information in `eshell-ls-file'.
This is passed to `format-time-string' as a format string.
To display the date using the current locale, use \"%b \%e\"."
  :version "24.1"
  :type 'string)

(defcustom eshell-ls-initial-args nil
  "If non-nil, this list of args is included before any call to `ls'.
This is useful for enabling human-readable format (-h), for example."
  :type '(repeat :tag "Arguments" string))

(defcustom eshell-ls-dired-initial-args nil
  "If non-nil, args is included before any call to `ls' in Dired.
This is useful for enabling human-readable format (-h), for example."
  :type '(repeat :tag "Arguments" string))

(defcustom eshell-ls-use-in-dired nil
  "If non-nil, use `eshell-ls' to read directories in Dired.
Changing this without using customize has no effect."
  :set (lambda (symbol value)
         (if value
             (advice-add 'insert-directory :around
                         #'eshell-ls--insert-directory)
           (advice-remove 'insert-directory
                          #'eshell-ls--insert-directory))
         (set symbol value))
  :type 'boolean
  :require 'em-ls)
(add-hook 'eshell-ls-unload-hook
          (lambda () (advice-remove 'insert-directory
                               #'eshell-ls--insert-directory)))


(defcustom eshell-ls-default-blocksize 1024
  "The default blocksize to use when display file sizes with -s."
  :type 'integer)

(defcustom eshell-ls-exclude-regexp nil
  "Unless -a is specified, files matching this regexp will not be shown."
  :type '(choice regexp (const nil)))

(defcustom eshell-ls-exclude-hidden t
  "Unless -a is specified, files beginning with . will not be shown.
Using this boolean, instead of `eshell-ls-exclude-regexp', is both
faster and conserves more memory."
  :type 'boolean)

(defcustom eshell-ls-use-colors t
  "If non-nil, use colors in file listings."
  :type 'boolean)

(defface eshell-ls-directory
  '((((class color) (background light)) (:foreground "Blue" :weight bold))
    (((class color) (background dark)) (:foreground "SkyBlue" :weight bold))
    (t (:weight bold)))
  "The face used for highlighting directories.")
(define-obsolete-face-alias 'eshell-ls-directory-face
  'eshell-ls-directory "22.1")

(defface eshell-ls-symlink
  '((((class color) (background light)) (:foreground "Dark Cyan" :weight bold))
    (((class color) (background dark)) (:foreground "Cyan" :weight bold)))
  "The face used for highlighting symbolic links.")
(define-obsolete-face-alias 'eshell-ls-symlink-face 'eshell-ls-symlink "22.1")

(defface eshell-ls-executable
  '((((class color) (background light)) (:foreground "ForestGreen" :weight bold))
    (((class color) (background dark)) (:foreground "Green" :weight bold)))
  "The face used for highlighting executables (not directories, though).")
(define-obsolete-face-alias 'eshell-ls-executable-face
  'eshell-ls-executable "22.1")

(defface eshell-ls-readonly
  '((((class color) (background light)) (:foreground "Brown"))
    (((class color) (background dark)) (:foreground "Pink")))
  "The face used for highlighting read-only files.")
(define-obsolete-face-alias 'eshell-ls-readonly-face 'eshell-ls-readonly "22.1")

(defface eshell-ls-unreadable
  '((((class color) (background light)) (:foreground "Grey30"))
    (((class color) (background dark)) (:foreground "DarkGrey")))
  "The face used for highlighting unreadable files.")
(define-obsolete-face-alias 'eshell-ls-unreadable-face
  'eshell-ls-unreadable "22.1")

(defface eshell-ls-special
  '((((class color) (background light)) (:foreground "Magenta" :weight bold))
    (((class color) (background dark)) (:foreground "Magenta" :weight bold)))
  "The face used for highlighting non-regular files.")
(define-obsolete-face-alias 'eshell-ls-special-face 'eshell-ls-special "22.1")

(defface eshell-ls-missing
  '((((class color) (background light)) (:foreground "Red" :weight bold))
    (((class color) (background dark)) (:foreground "Red" :weight bold)))
  "The face used for highlighting non-existent file names.")
(define-obsolete-face-alias 'eshell-ls-missing-face 'eshell-ls-missing "22.1")

(defcustom eshell-ls-archive-regexp
  (concat "\\.\\(t\\(a[rz]\\|gz\\)\\|arj\\|lzh\\|"
          "zip\\|[zZ]\\|gz\\|bz2\\|xz\\|deb\\|rpm\\)\\'")
  "A regular expression that matches names of file archives.
This typically includes both traditional archives and compressed
files."
  :version "24.1"                       ; added xz
  :type 'regexp)

(defface eshell-ls-archive
  '((((class color) (background light)) (:foreground "Orchid" :weight bold))
    (((class color) (background dark)) (:foreground "Orchid" :weight bold)))
  "The face used for highlighting archived and compressed file names.")
(define-obsolete-face-alias 'eshell-ls-archive-face 'eshell-ls-archive "22.1")

(defcustom eshell-ls-backup-regexp
  "\\(\\`\\.?#\\|\\(\\.bak\\|~\\)\\'\\)"
  "A regular expression that matches names of backup files."
  :type 'regexp)

(defface eshell-ls-backup
  '((((class color) (background light)) (:foreground "OrangeRed"))
    (((class color) (background dark)) (:foreground "LightSalmon")))
  "The face used for highlighting backup file names.")
(define-obsolete-face-alias 'eshell-ls-backup-face 'eshell-ls-backup "22.1")

(defcustom eshell-ls-product-regexp
  "\\.\\(elc\\|o\\(bj\\)?\\|a\\|lib\\|res\\)\\'"
  "A regular expression that matches names of product files.
Products are files that get generated from a source file, and hence
ought to be recreatable if they are deleted."
  :type 'regexp)

(defface eshell-ls-product
  '((((class color) (background light)) (:foreground "OrangeRed"))
    (((class color) (background dark)) (:foreground "LightSalmon")))
  "The face used for highlighting files that are build products.")
(define-obsolete-face-alias 'eshell-ls-product-face 'eshell-ls-product "22.1")

(defcustom eshell-ls-clutter-regexp
  "\\(^texput\\.log\\|^core\\)\\'"
  "A regular expression that matches names of junk files.
These are mainly files that get created for various reasons, but don't
really need to stick around for very long."
  :type 'regexp)

(defface eshell-ls-clutter
  '((((class color) (background light)) (:foreground "OrangeRed" :weight bold))
    (((class color) (background dark)) (:foreground "OrangeRed" :weight bold)))
  "The face used for highlighting junk file names.")
(define-obsolete-face-alias 'eshell-ls-clutter-face 'eshell-ls-clutter "22.1")

(defsubst eshell-ls-filetype-p (attrs type)
  "Test whether ATTRS specifies a directory."
  (if (nth 8 attrs)
      (eq (aref (nth 8 attrs) 0) type)))

(defmacro eshell-ls-applicable (attrs index func file)
  "Test whether, for ATTRS, the user can do what corresponds to INDEX.
ATTRS is a string of file modes.  See `file-attributes'.
If we cannot determine the answer using ATTRS (e.g., if we need
to know what group the user is in), compute the return value by
calling FUNC with FILE as an argument."
  `(let ((owner (nth 2 ,attrs))
         (modes (nth 8 ,attrs)))
     (cond ((cond ((numberp owner)
                   (= owner (user-uid)))
                  ((stringp owner)
                   (or (string-equal owner (user-login-name))
                       (member owner (eshell-current-ange-uids)))))
            ;; The user owns this file.
            (not (eq (aref modes ,index) ?-)))
           ((eq (aref modes (+ ,index 3))
                (aref modes (+ ,index 6)))
            ;; If the "group" and "other" fields give identical
            ;; results, use that.
            (not (eq (aref modes (+ ,index 3)) ?-)))
           (t
            ;; Otherwise call FUNC.
            (,(eval func) ,file)))))

(defcustom eshell-ls-highlight-alist nil
  "This alist correlates test functions to color.
The format of the members of this alist is

  (TEST-SEXP . FACE)

If TEST-SEXP evals to non-nil, that face will be used to highlight the
name of the file.  The first match wins.  `file' and `attrs' are in
scope during the evaluation of TEST-SEXP."
  :type '(repeat (cons function face)))

(defvar block-size)
(defvar dereference-links)
(defvar dir-literal)
(defvar error-func)
(defvar flush-func)
(defvar human-readable)
(defvar ignore-pattern)
(defvar insert-func)
(defvar listing-style)
(defvar numeric-uid-gid)
(defvar reverse-list)
(defvar show-all)
(defvar show-almost-all)
(defvar show-recursive)
(defvar show-size)
(defvar sort-method)
(defvar ange-cache)
(defvar dired-flag)

;;; Functions:

(defun eshell-ls--insert-directory
  (orig-fun file switches &optional wildcard full-directory-p)
  "Insert directory listing for FILE, formatted according to SWITCHES.
Leaves point after the inserted text.
SWITCHES may be a string of options, or a list of strings.
Optional third arg WILDCARD means treat FILE as shell wildcard.
Optional fourth arg FULL-DIRECTORY-P means file is a directory and
switches do not contain `d', so that a full listing is expected.

This version of the function uses `eshell/ls'.  If any of the switches
passed are not recognized, the operating system's version will be used
instead."
  (if (not eshell-ls-use-in-dired)
      (funcall orig-fun file switches wildcard full-directory-p)
    (let ((handler (find-file-name-handler file 'insert-directory)))
      (if handler
          (funcall handler 'insert-directory file switches
                   wildcard full-directory-p)
        (if (stringp switches)
            (setq switches (split-string switches)))
        (let (eshell-current-handles
              eshell-current-subjob-p
              font-lock-mode)
          ;; use the fancy highlighting in `eshell-ls' rather than font-lock
          (when (and eshell-ls-use-colors
                     (featurep 'font-lock))
            (font-lock-mode -1)
            (setq font-lock-defaults nil)
            (if (boundp 'font-lock-buffers)
                (set 'font-lock-buffers
                     (delq (current-buffer)
                           (symbol-value 'font-lock-buffers)))))
          (let ((insert-func 'insert)
                (error-func 'insert)
                (flush-func 'ignore)
                eshell-ls-dired-initial-args)
            (eshell-do-ls (append switches (list file)))))))))

(defsubst eshell/ls (&rest args)
  "An alias version of `eshell-do-ls'."
  (let ((insert-func 'eshell-buffered-print)
        (error-func 'eshell-error)
        (flush-func 'eshell-flush))
    (apply 'eshell-do-ls args)))

(put 'eshell/ls 'eshell-no-numeric-conversions t)

(declare-function eshell-glob-regexp "em-glob" (pattern))

(defun eshell-do-ls (&rest args)
  "Implementation of \"ls\" in Lisp, passing ARGS."
  (funcall flush-func -1)
  ;; Process the command arguments, and begin listing files.
  (eshell-eval-using-options
   "ls" (if eshell-ls-initial-args
            (list eshell-ls-initial-args args)
          args)
   `((?a "all" nil show-all
         "do not ignore entries starting with .")
     (?A "almost-all" nil show-almost-all
         "do not list implied . and ..")
     (?c nil by-ctime sort-method
         "sort by last status change time")
     (?d "directory" nil dir-literal
         "list directory entries instead of contents")
     (?k "kilobytes" 1024 block-size
         "using 1024 as the block size")
     (?h "human-readable" 1024 human-readable
         "print sizes in human readable format")
     (?H "si" 1000 human-readable
         "likewise, but use powers of 1000 not 1024")
     (?I "ignore" t ignore-pattern
         "do not list implied entries matching pattern")
     (?l nil long-listing listing-style
         "use a long listing format")
     (?n "numeric-uid-gid" nil numeric-uid-gid
         "list numeric UIDs and GIDs instead of names")
     (?r "reverse" nil reverse-list
         "reverse order while sorting")
     (?s "size" nil show-size
         "print size of each file, in blocks")
     (?t nil by-mtime sort-method
         "sort by modification time")
     (?u nil by-atime sort-method
         "sort by last access time")
     (?x nil by-lines listing-style
         "list entries by lines instead of by columns")
     (?C nil by-columns listing-style
         "list entries by columns")
     (?L "dereference" nil dereference-links
         "list entries pointed to by symbolic links")
     (?R "recursive" nil show-recursive
         "list subdirectories recursively")
     (?S nil by-size sort-method
         "sort by file size")
     (?U nil unsorted sort-method
         "do not sort; list entries in directory order")
     (?X nil by-extension sort-method
         "sort alphabetically by entry extension")
     (?1 nil single-column listing-style
         "list one file per line")
     (nil "dired" nil dired-flag
          "Here for compatibility with GNU ls.")
     (nil "help" nil nil
          "show this usage display")
     :external "ls"
     :usage "[OPTION]... [FILE]...
List information about the FILEs (the current directory by default).
Sort entries alphabetically across.")
   ;; setup some defaults, based on what the user selected
   (unless block-size
     (setq block-size eshell-ls-default-blocksize))
   (unless listing-style
     (setq listing-style 'by-columns))
   (unless args
     (setq args (list ".")))
   (let ((eshell-ls-exclude-regexp eshell-ls-exclude-regexp) ange-cache)
     (when ignore-pattern
       (unless (eshell-using-module 'eshell-glob)
         (error (concat "-I option requires that `eshell-glob'"
                        " be a member of `eshell-modules-list'")))
       (set-text-properties 0 (length ignore-pattern) nil ignore-pattern)
       (setq eshell-ls-exclude-regexp
             (if eshell-ls-exclude-regexp
                 (concat "\\(" eshell-ls-exclude-regexp "\\|"
                         (eshell-glob-regexp ignore-pattern) "\\)")
               (eshell-glob-regexp ignore-pattern))))
     ;; list the files!
     (eshell-ls-entries
      (mapcar (lambda (arg)
                (cons (if (and (eshell-under-windows-p)
                               (file-name-absolute-p arg))
                          (expand-file-name arg)
                        arg)
                      (eshell-file-attributes
                       arg (if numeric-uid-gid 'integer 'string))))
              args)
      t (expand-file-name default-directory)))
   (funcall flush-func)))

(defsubst eshell-ls-printable-size (filesize &optional by-blocksize)
  "Return a printable FILESIZE."
  (eshell-printable-size filesize human-readable
                         (and by-blocksize block-size)
                         eshell-ls-use-colors))

(defsubst eshell-ls-size-string (attrs size-width)
  "Return the size string for ATTRS length, using SIZE-WIDTH."
  (let* ((str (eshell-ls-printable-size (nth 7 attrs) t))
         (len (length str)))
    (if (< len size-width)
        (concat (make-string (- size-width len) ? ) str)
      str)))

(defun eshell-ls-annotate (fileinfo)
  "Given a FILEINFO object, return a resolved, decorated FILEINFO.
This means resolving any symbolic links, determining what face the
name should be displayed as, etc.  Think of it as cooking a FILEINFO."
  (if (not (and (stringp (cadr fileinfo))
                (or dereference-links
                    (eq listing-style 'long-listing))))
      (setcar fileinfo (eshell-ls-decorated-name fileinfo))
    (let (dir attr)
      (unless (file-name-absolute-p (cadr fileinfo))
        (setq dir (file-truename
                   (file-name-directory
                    (expand-file-name (car fileinfo))))))
      (setq attr
            (eshell-file-attributes
             (let ((target (if dir
                               (expand-file-name (cadr fileinfo) dir)
                             (cadr fileinfo))))
               (if dereference-links
                   (file-truename target)
                 target))))
      (if (or dereference-links
              (string-match "^\\.\\.?$" (car fileinfo)))
          (progn
            (setcdr fileinfo attr)
            (setcar fileinfo (eshell-ls-decorated-name fileinfo)))
        (cl-assert (eq listing-style 'long-listing))
        (setcar fileinfo
                (concat (eshell-ls-decorated-name fileinfo) " -> "
                        (eshell-ls-decorated-name
                         (cons (cadr fileinfo) attr)))))))
  fileinfo)

(defun eshell-ls-file (fileinfo &optional size-width copy-fileinfo)
  "Output FILE in long format.
FILE may be a string, or a cons cell whose car is the filename and
whose cdr is the list of file attributes."
  (if (not (cdr fileinfo))
      (funcall error-func (format "%s: No such file or directory\n"
                                  (car fileinfo)))
    (setq fileinfo
          (eshell-ls-annotate (if copy-fileinfo
                                  (cons (car fileinfo)
                                        (cdr fileinfo))
                                fileinfo)))
    (let ((file (car fileinfo))
          (attrs (cdr fileinfo)))
      (if (not (eq listing-style 'long-listing))
          (if show-size
              (funcall insert-func (eshell-ls-size-string attrs size-width)
                       " " file "\n")
            (funcall insert-func file "\n"))
        (let ((line
               (concat
                (if show-size
                    (concat (eshell-ls-size-string attrs size-width) " "))
                (format
                 (if numeric-uid-gid
                     "%s%4d %-8s %-8s "
                   "%s%4d %-14s %-8s ")
                 (or (nth 8 attrs) "??????????")
                 (or (nth 1 attrs) 0)
                 (or (let ((user (nth 2 attrs)))
                       (and (stringp user)
                            (eshell-substring user 14)))
                     (nth 2 attrs)
                     "")
                 (or (let ((group (nth 3 attrs)))
                       (and (stringp group)
                            (eshell-substring group 8)))
                     (nth 3 attrs)
                     ""))
                (let* ((str (eshell-ls-printable-size (nth 7 attrs)))
                       (len (length str)))
                  ;; Let file sizes shorter than 9 align neatly.
                  (if (< len (or size-width 8))
                      (concat (make-string (- (or size-width 8) len) ? ) str)
                    str))
                " " (format-time-string
                     (concat
                      eshell-ls-date-format " "
                      (if (= (nth 5 (decode-time (current-time)))
                             (nth 5 (decode-time
                                     (nth (cond
                                           ((eq sort-method 'by-atime) 4)
                                           ((eq sort-method 'by-ctime) 6)
                                           (t 5)) attrs))))
                          "%H:%M"
                        " %Y")) (nth (cond
                        ((eq sort-method 'by-atime) 4)
                        ((eq sort-method 'by-ctime) 6)
                        (t 5)) attrs)) " ")))
          (funcall insert-func line file "\n"))))))

(defun eshell-ls-dir (dirinfo &optional insert-name root-dir size-width)
  "Output the entries in DIRINFO.
If INSERT-NAME is non-nil, the name of DIRINFO will be output.  If
ROOT-DIR is also non-nil, and a directory name, DIRINFO will be output
relative to that directory."
  (let ((dir (car dirinfo)))
    (if (not (cdr dirinfo))
        (funcall error-func (format "%s: No such file or directory\n" dir))
      (if dir-literal
          (eshell-ls-file dirinfo size-width)
        (if insert-name
            (funcall insert-func
                     (eshell-ls-decorated-name
                      (cons (concat
                             (if root-dir
                                 (file-relative-name dir root-dir)
                               (expand-file-name dir)))
                            (cdr dirinfo))) ":\n"))
        (let ((entries (eshell-directory-files-and-attributes
                        dir nil (and (not (or show-all show-almost-all))
                                     eshell-ls-exclude-hidden
                                     "\\`[^.]") t
                                     ;; Asking for UID and GID as
                                     ;; strings saves another syscall
                                     ;; later when we are going to
                                     ;; display user and group names.
                                     (if numeric-uid-gid 'integer 'string))))
          (when (and show-almost-all
                     (not show-all))
            (setq entries
                  (cl-remove-if
                   (lambda (entry)
                     (member (car entry) '("." "..")))
                   entries)))
          (when (and (not (or show-all show-almost-all))
                     eshell-ls-exclude-regexp)
            (while (and entries (string-match eshell-ls-exclude-regexp
                                              (caar entries)))
              (setq entries (cdr entries)))
            (let ((e entries))
              (while (cdr e)
                (if (string-match eshell-ls-exclude-regexp (car (cadr e)))
                    (setcdr e (cddr e))
                  (setq e (cdr e))))))
          (when (or (eq listing-style 'long-listing) show-size)
            (let ((total 0.0))
              (setq size-width 0)
              (dolist (e entries)
                (if (nth 7 (cdr e))
                    (setq total (+ total (nth 7 (cdr e)))
                          size-width
                          (max size-width
                               (length (eshell-ls-printable-size
                                        (nth 7 (cdr e))
                                        (not
                                         ;; If we are under -l, count length
                                         ;; of sizes in bytes, not in blocks.
                                         (eq listing-style 'long-listing))))))))
              (funcall insert-func "total "
                       (eshell-ls-printable-size total t) "\n")))
          (let ((default-directory (expand-file-name dir)))
            (if show-recursive
                (eshell-ls-entries
                 (let ((e entries) (good-entries (list t)))
                   (while e
                     (unless (let ((len (length (caar e))))
                               (and (eq (aref (caar e) 0) ?.)
                                    (or (= len 1)
                                        (and (= len 2)
                                             (eq (aref (caar e) 1) ?.)))))
                       (nconc good-entries (list (car e))))
                     (setq e (cdr e)))
                   (cdr good-entries))
                 nil root-dir)
              (eshell-ls-files (eshell-ls-sort-entries entries)
                               size-width))))))))

(defsubst eshell-ls-compare-entries (l r inx func)
  "Compare the time of two files, L and R, the attribute indexed by INX."
  (let ((lt (nth inx (cdr l)))
        (rt (nth inx (cdr r))))
    (if (equal lt rt)
        (string-lessp (directory-file-name (car l))
                      (directory-file-name (car r)))
      (funcall func rt lt))))

(defun eshell-ls-sort-entries (entries)
  "Sort the given ENTRIES, which may be files, directories or both.
In Eshell's implementation of ls, ENTRIES is always reversed."
  (if (eq sort-method 'unsorted)
      (nreverse entries)
    (sort entries
          (function
           (lambda (l r)
             (let ((result
                    (cond
                     ((eq sort-method 'by-atime)
                      (eshell-ls-compare-entries l r 4 'time-less-p))
                     ((eq sort-method 'by-mtime)
                      (eshell-ls-compare-entries l r 5 'time-less-p))
                     ((eq sort-method 'by-ctime)
                      (eshell-ls-compare-entries l r 6 'time-less-p))
                     ((eq sort-method 'by-size)
                      (eshell-ls-compare-entries l r 7 '<))
                     ((eq sort-method 'by-extension)
                      (let ((lx (file-name-extension
                                 (directory-file-name (car l))))
                            (rx (file-name-extension
                                 (directory-file-name (car r)))))
                        (cond
                         ((or (and (not lx) (not rx))
                              (equal lx rx))
                          (string-lessp (directory-file-name (car l))
                                        (directory-file-name (car r))))
                         ((not lx) t)
                         ((not rx) nil)
                         (t
                          (string-lessp lx rx)))))
                     (t
                      (string-lessp (directory-file-name (car l))
                                    (directory-file-name (car r)))))))
               (if reverse-list
                   (not result)
                 result)))))))

(defun eshell-ls-files (files &optional size-width copy-fileinfo)
  "Output a list of FILES.
Each member of FILES is either a string or a cons cell of the form
\(FILE .  ATTRS)."
  ;; Mimic behavior of coreutils ls, which lists a single file per
  ;; line when output is not a tty.  Exceptions: if -x was supplied,
  ;; or if we are the _last_ command in a pipeline.
  ;; FIXME Not really the same since not testing output destination.
  (if (or (and eshell-in-pipeline-p
               (not (eq eshell-in-pipeline-p 'last))
               (not (eq listing-style 'by-lines)))
          (memq listing-style '(long-listing single-column)))
      (dolist (file files)
        (if file
            (eshell-ls-file file size-width copy-fileinfo)))
    (let ((f files)
          last-f
          display-files
          ignore)
      (while f
        (if (cdar f)
            (setq last-f f
                  f (cdr f))
          (unless ignore
            (funcall error-func
                     (format "%s: No such file or directory\n" (caar f))))
          (if (eq f files)
              (setq files (cdr files)
                    f files)
            (if (not (cdr f))
                (progn
                  (setcdr last-f nil)
                  (setq f nil))
              (setcar f (cadr f))
              (setcdr f (cddr f))))))
      (if (not show-size)
          (setq display-files (mapcar 'eshell-ls-annotate files))
        (dolist (file files)
          (let* ((str (eshell-ls-printable-size (nth 7 (cdr file)) t))
                 (len (length str)))
            (if (< len size-width)
                (setq str (concat (make-string (- size-width len) ? ) str)))
            (setq file (eshell-ls-annotate file)
                  display-files (cons (cons (concat str " " (car file))
                                            (cdr file))
                                      display-files))))
        (setq display-files (nreverse display-files)))
      (let* ((col-vals
              (if (eq listing-style 'by-columns)
                  (eshell-ls-find-column-lengths display-files)
                (cl-assert (eq listing-style 'by-lines))
                (eshell-ls-find-column-widths display-files)))
             (col-widths (car col-vals))
             (display-files (cdr col-vals))
             (columns (length col-widths))
             (col-index 1)
             need-return)
        (dolist (file display-files)
          (let ((name
                 (if (car file)
                     (if show-size
                         (concat (substring (car file) 0 size-width)
                                 (eshell-ls-decorated-name
                                  (cons (substring (car file) size-width)
                                        (cdr file))))
                       (eshell-ls-decorated-name file))
                   "")))
            (if (< col-index columns)
                (setq need-return
                      (concat need-return name
                              (make-string
                               (max 0 (- (aref col-widths
                                               (1- col-index))
                                         (length name))) ? ))
                      col-index (1+ col-index))
              (funcall insert-func need-return name "\n")
              (setq col-index 1 need-return nil))))
        (if need-return
            (funcall insert-func need-return "\n"))))))

(defun eshell-ls-entries (entries &optional separate root-dir)
  "Output PATH's directory ENTRIES.
Each member of ENTRIES may either be a string or a cons cell, the car
of which is the file name, and the cdr of which is the list of
attributes.
If SEPARATE is non-nil, directories name will be entirely separated
from the filenames.  This is the normal behavior, except when doing a
recursive listing.
ROOT-DIR, if non-nil, specifies the root directory of the listing, to
which non-absolute directory names will be made relative if ever they
need to be printed."
  (let (dirs files show-names need-return (size-width 0))
    (dolist (entry entries)
      (if (and (not dir-literal)
               (or (eshell-ls-filetype-p (cdr entry) ?d)
                   (and (eshell-ls-filetype-p (cdr entry) ?l)
                        (file-directory-p (car entry)))))
          (progn
            (unless separate
              (setq files (cons entry files)
                    size-width
                    (if show-size
                        (max size-width
                             (length (eshell-ls-printable-size
                                      (nth 7 (cdr entry)) t))))))
            (setq dirs (cons entry dirs)))
        (setq files (cons entry files)
              size-width
              (if show-size
                  (max size-width
                       (length (eshell-ls-printable-size
                                (nth 7 (cdr entry)) t)))))))
    (when files
      (eshell-ls-files (eshell-ls-sort-entries files)
                       size-width show-recursive)
      (setq need-return t))
    (setq show-names (or show-recursive
                         (> (+ (length files) (length dirs)) 1)))
    (dolist (dir (eshell-ls-sort-entries dirs))
      (if (and need-return (not dir-literal))
          (funcall insert-func "\n"))
      (eshell-ls-dir dir show-names
                     (unless (file-name-absolute-p (car dir)) root-dir)
                     size-width)
      (setq need-return t))))

(defun eshell-ls-find-column-widths (files)
  "Find the best fitting column widths for FILES.
It will be returned as a vector, whose length is the number of columns
to use, and each member of which is the width of that column
\(including spacing)."
  (let* ((numcols 0)
         (width 0)
         (widths
          (mapcar
           (function
            (lambda (file)
              (+ 2 (length (car file)))))
           files))
         ;; must account for the added space...
         (max-width (+ (window-width) 2))
         (best-width 0)
         col-widths)

    ;; determine the largest number of columns in the first row
    (let ((w widths))
      (while (and w (< width max-width))
        (setq width (+ width (car w))
              numcols (1+ numcols)
              w (cdr w))))

    ;; refine it based on the following rows
    (while (> numcols 0)
      (let ((i 0)
            (colw (make-vector numcols 0))
            (w widths))
        (while w
          (if (= i numcols)
              (setq i 0))
          (aset colw i (max (aref colw i) (car w)))
          (setq w (cdr w) i (1+ i)))
        (setq i 0 width 0)
        (while (< i numcols)
          (setq width (+ width (aref colw i))
                i (1+ i)))
        (if (and (< width max-width)
                 (> width best-width))
            (setq col-widths colw
                  best-width width)))
      (setq numcols (1- numcols)))

    (cons (or col-widths (vector max-width)) files)))

(defun eshell-ls-find-column-lengths (files)
  "Find the best fitting column lengths for FILES.
It will be returned as a vector, whose length is the number of columns
to use, and each member of which is the width of that column
\(including spacing)."
  (let* ((numcols 1)
         (width 0)
         (widths
          (mapcar
           (function
            (lambda (file)
              (+ 2 (length (car file)))))
           files))
         (max-width (+ (window-width) 2))
         col-widths
         colw)

    ;; refine it based on the following rows
    (while numcols
      (let* ((rows (ceiling (/ (length widths)
                               (float numcols))))
             (w widths)
             (len (* rows numcols))
             (index 0)
             (i 0))
        (setq width 0)
        (unless (or (= rows 0)
                    (<= (/ (length widths) (float rows))
                        (float (1- numcols))))
          (setq colw (make-vector numcols 0))
          (while (> len 0)
            (if (= i numcols)
                (setq i 0 index (1+ index)))
            (aset colw i
                  (max (aref colw i)
                       (or (nth (+ (* i rows) index) w) 0)))
            (setq len (1- len) i (1+ i)))
          (setq i 0)
          (while (< i numcols)
            (setq width (+ width (aref colw i))
                  i (1+ i))))
        (if (>= width max-width)
            (setq numcols nil)
          (if colw
              (setq col-widths colw))
          (if (>= numcols (length widths))
              (setq numcols nil)
            (setq numcols (1+ numcols))))))

    (if (not col-widths)
        (cons (vector max-width) files)
      (setq numcols (length col-widths))
      (let* ((rows (ceiling (/ (length widths)
                               (float numcols))))
             (len (* rows numcols))
             (newfiles (make-list len nil))
             (index 0)
             (i 0)
             (j 0))
        (while (< j len)
          (if (= i numcols)
              (setq i 0 index (1+ index)))
          (setcar (nthcdr j newfiles)
                  (nth (+ (* i rows) index) files))
          (setq j (1+ j) i (1+ i)))
        (cons col-widths newfiles)))))

(defun eshell-ls-decorated-name (file)
  "Return FILE, possibly decorated."
  (if eshell-ls-use-colors
      (let ((face
             (cond
              ((not (cdr file))
               'eshell-ls-missing)

              ((stringp (cadr file))
               'eshell-ls-symlink)

              ((eq (cadr file) t)
               'eshell-ls-directory)

              ((not (eshell-ls-filetype-p (cdr file) ?-))
               'eshell-ls-special)

              ((and (/= (user-uid) 0) ; root can execute anything
                    (eshell-ls-applicable (cdr file) 3
                                          'file-executable-p (car file)))
               'eshell-ls-executable)

              ((not (eshell-ls-applicable (cdr file) 1
                                          'file-readable-p (car file)))
               'eshell-ls-unreadable)

              ((string-match eshell-ls-archive-regexp (car file))
               'eshell-ls-archive)

              ((string-match eshell-ls-backup-regexp (car file))
               'eshell-ls-backup)

              ((string-match eshell-ls-product-regexp (car file))
               'eshell-ls-product)

              ((string-match eshell-ls-clutter-regexp (car file))
               'eshell-ls-clutter)

              ((not (eshell-ls-applicable (cdr file) 2
                                          'file-writable-p (car file)))
               'eshell-ls-readonly)
              (eshell-ls-highlight-alist
               (let ((tests eshell-ls-highlight-alist)
                     value)
                 (while tests
                   (if (funcall (caar tests) (car file) (cdr file))
                       (setq value (cdar tests) tests nil)
                     (setq tests (cdr tests))))
                 value)))))
        (if face
            (add-text-properties 0 (length (car file))
                                 (list 'font-lock-face face)
                                 (car file)))))
  (car file))

(provide 'em-ls)

(require 'esh-mode)
(eval-when-compile (require 'eshell))

;;;###autoload
(progn
(defgroup eshell-prompt nil
  "This module provides command prompts, and navigation between them,
as is common with most shells."
  :tag "Command prompts"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-prompt-load-hook nil
  "A list of functions to call when loading `eshell-prompt'."
  :version "24.1"                       ; removed eshell-prompt-initialize
  :type 'hook
  :group 'eshell-prompt)

(autoload 'eshell/pwd "em-dirs")

(defcustom eshell-prompt-function
  (function
   (lambda ()
     (concat (abbreviate-file-name (eshell/pwd))
             (if (= (user-uid) 0) " # " " $ "))))
  "A function that returns the Eshell prompt string.
Make sure to update `eshell-prompt-regexp' so that it will match your
prompt."
  :type 'function
  :group 'eshell-prompt)

(defcustom eshell-prompt-regexp "^[^#$\n]* [#$] "
  "A regexp which fully matches your eshell prompt.
This setting is important, since it affects how eshell will interpret
the lines that are passed to it.
If this variable is changed, all Eshell buffers must be exited and
re-entered for it to take effect."
  :type 'regexp
  :group 'eshell-prompt)

(defcustom eshell-highlight-prompt t
  "If non-nil, Eshell should highlight the prompt."
  :type 'boolean
  :group 'eshell-prompt)

(defface eshell-prompt
  '((default :weight bold)
    (((class color) (background light)) :foreground "Red")
    (((class color) (background dark))  :foreground "Pink"))
  "The face used to highlight prompt strings.
For highlighting other kinds of strings -- similar to shell mode's
behavior -- simply use an output filer which changes text properties."
  :group 'eshell-prompt)
(define-obsolete-face-alias 'eshell-prompt-face 'eshell-prompt "22.1")

(defcustom eshell-before-prompt-hook nil
  "A list of functions to call before outputting the prompt."
  :type 'hook
  :options '(eshell-begin-on-new-line)
  :group 'eshell-prompt)

(defcustom eshell-after-prompt-hook nil
  "A list of functions to call after outputting the prompt.
Note that if `eshell-scroll-show-maximum-output' is non-nil, then
setting `eshell-show-maximum-output' here won't do much.  It depends
on whether the user wants the resizing to happen while output is
arriving, or after."
  :type 'hook
  :options '(eshell-show-maximum-output)
  :group 'eshell-prompt)

;;; Functions:

(defun eshell-prompt-initialize ()
  "Initialize the prompting code."
  (unless eshell-non-interactive-p
    (add-hook 'eshell-post-command-hook 'eshell-emit-prompt nil t)

    (make-local-variable 'eshell-prompt-regexp)
    (if eshell-prompt-regexp
        (set (make-local-variable 'paragraph-start) eshell-prompt-regexp))

    (set (make-local-variable 'eshell-skip-prompt-function)
         'eshell-skip-prompt)

    (define-key eshell-command-map [(control ?n)] 'eshell-next-prompt)
    (define-key eshell-command-map [(control ?p)] 'eshell-previous-prompt)))

(defun eshell-emit-prompt ()
  "Emit a prompt if eshell is being used interactively."
  (run-hooks 'eshell-before-prompt-hook)
  (if (not eshell-prompt-function)
      (set-marker eshell-last-output-end (point))
    (let ((prompt (funcall eshell-prompt-function)))
      (and eshell-highlight-prompt
           (add-text-properties 0 (length prompt)
                                ;; '(read-only t
                                ;;   font-lock-face eshell-prompt
                                ;;   front-sticky (font-lock-face read-only)
                                ;;   rear-nonsticky (font-lock-face read-only))
                                '(read-only nil
                                  font-lock-face eshell-prompt)
                                prompt))
      (eshell-interactive-print prompt)))
  (run-hooks 'eshell-after-prompt-hook))

(defun eshell-backward-matching-input (regexp arg)
  "Search backward through buffer for match for REGEXP.
Matches are searched for on lines that match `eshell-prompt-regexp'.
With prefix argument N, search for Nth previous match.
If N is negative, find the next or Nth next match."
  (interactive (eshell-regexp-arg "Backward input matching (regexp): "))
  (let* ((re (concat eshell-prompt-regexp ".*" regexp))
         (pos (save-excursion (end-of-line (if (> arg 0) 0 1))
                              (if (re-search-backward re nil t arg)
                                  (point)))))
    (if (null pos)
        (progn (message "Not found")
               (ding))
      (goto-char pos)
      (eshell-bol))))

(defun eshell-forward-matching-input (regexp arg)
  "Search forward through buffer for match for REGEXP.
Matches are searched for on lines that match `eshell-prompt-regexp'.
With prefix argument N, search for Nth following match.
If N is negative, find the previous or Nth previous match."
  (interactive (eshell-regexp-arg "Forward input matching (regexp): "))
  (eshell-backward-matching-input regexp (- arg)))

(defun eshell-next-prompt (n)
  "Move to end of Nth next prompt in the buffer.
See `eshell-prompt-regexp'."
  (interactive "p")
  (forward-paragraph n)
  (eshell-skip-prompt))

(defun eshell-previous-prompt (n)
  "Move to end of Nth previous prompt in the buffer.
See `eshell-prompt-regexp'."
  (interactive "p")
  (eshell-next-prompt (- (1+ n))))

(defun eshell-skip-prompt ()
  "Skip past the text matching regexp `eshell-prompt-regexp'.
If this takes us past the end of the current line, don't skip at all."
  (let ((eol (line-end-position)))
    (if (and (looking-at eshell-prompt-regexp)
             (<= (match-end 0) eol))
        (goto-char (match-end 0)))))

(provide 'em-prompt)

;; Local Variables:
;; generated-autoload-file: "esh-groups.el"
;; End:

;;; em-prompt.el ends here

(require 'esh-mode)
(eval-when-compile (require 'eshell))

;;;###autoload
(progn
(defgroup eshell-rebind nil
  "This module allows for special keybindings that only take effect
while the point is in a region of input text.  By default, it binds
C-a to move to the beginning of the input text (rather than just the
beginning of the line), and C-p and C-n to move through the input
history, C-u kills the current input text, etc.  It also, if
`eshell-confine-point-to-input' is non-nil, does not allow certain
commands to cause the point to leave the input area, such as
`backward-word', `previous-line', etc.  This module intends to mimic
the behavior of normal shells while the user editing new input text."
  :tag "Rebind keys at input"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-rebind-load-hook nil
  "A list of functions to call when loading `eshell-rebind'."
  :version "24.1"                       ; removed eshell-rebind-initialize
  :type 'hook
  :group 'eshell-rebind)

(defcustom eshell-rebind-keys-alist
  '(([(control ?a)] . eshell-bol)
    ([home]         . eshell-bol)
    ([(control ?d)] . eshell-delchar-or-maybe-eof)
    ([backspace]    . eshell-delete-backward-char)
    ([delete]       . eshell-delete-backward-char)
    ([(control ?w)] . backward-kill-word)
    ([(control ?u)] . eshell-kill-input))
  "Bind some keys differently if point is in input text."
  :type '(repeat (cons (vector :tag "Keys to bind"
                               (repeat :inline t sexp))
                       (function :tag "Command")))
  :group 'eshell-rebind)

(defcustom eshell-confine-point-to-input t
  "If non-nil, do not allow the point to leave the current input.
This is more difficult to do nicely in Emacs than one might think.
Basically, the `point-left' attribute is added to the input text, and
a function is placed on that hook to take the point back to
`eshell-last-output-end' every time the user tries to move away.  But
since there are many cases in which the point _ought_ to move away
\(for programmatic reasons), the variable
`eshell-cannot-leave-input-list' defines commands which are affected
from this rule.  However, this list is by no means as complete as it
probably should be, so basically all one can hope for is that other
people will left the point alone in the Eshell buffer.  Sigh."
  :type 'boolean
  :group 'eshell-rebind)

(defcustom eshell-error-if-move-away t
  "If non-nil, consider it an error to try to move outside current input.
This is default behavior of shells like bash."
  :type 'boolean
  :group 'eshell-rebind)

(defcustom eshell-remap-previous-input t
  "If non-nil, remap input keybindings on previous prompts as well."
  :type 'boolean
  :group 'eshell-rebind)

(defcustom eshell-cannot-leave-input-list
  '(beginning-of-line-text
    beginning-of-line
    move-to-column
    move-to-left-margin
    move-to-tab-stop
    forward-char
    backward-char
    delete-char
    delete-backward-char
    backward-delete-char
    backward-delete-char-untabify
    kill-paragraph
    backward-kill-paragraph
    kill-sentence
    backward-kill-sentence
    kill-sexp
    backward-kill-sexp
    kill-word
    backward-kill-word
    kill-region
    forward-list
    backward-list
    forward-page
    backward-page
    forward-point
    forward-paragraph
    backward-paragraph
    backward-prefix-chars
    forward-sentence
    backward-sentence
    forward-sexp
    backward-sexp
    forward-to-indentation
    backward-to-indentation
    backward-up-list
    forward-word
    backward-word
    forward-line
    previous-line
    next-line
    forward-visible-line
    forward-comment
    forward-thing)
  "A list of commands that cannot leave the input area."
  :type '(repeat function)
  :group 'eshell-rebind)

;; Internal Variables:

(defvar eshell-input-keymap)
(defvar eshell-previous-point)
(defvar eshell-lock-keymap)

;;; Functions:

(defun eshell-rebind-initialize ()
  "Initialize the inputting code."
  (unless eshell-non-interactive-p
    (add-hook 'eshell-mode-hook 'eshell-setup-input-keymap nil t)
    (make-local-variable 'eshell-previous-point)
    (add-hook 'pre-command-hook 'eshell-save-previous-point nil t)
    (make-local-variable 'overriding-local-map)
    (add-hook 'post-command-hook 'eshell-rebind-input-map nil t)
    (set (make-local-variable 'eshell-lock-keymap) nil)
    (define-key eshell-command-map [(meta ?l)] 'eshell-lock-local-map)))

(defun eshell-lock-local-map (&optional arg)
  "Lock or unlock the current local keymap.
Within a prefix arg, set the local keymap to its normal value, and
lock it at that."
  (interactive "P")
  (if (or arg (not eshell-lock-keymap))
      (progn
        (use-local-map eshell-mode-map)
        (setq eshell-lock-keymap t)
        (message "Local keymap locked in normal mode"))
    (use-local-map eshell-input-keymap)
    (setq eshell-lock-keymap nil)
    (message "Local keymap unlocked: obey context")))

(defun eshell-save-previous-point ()
  "Save the location of point before the next command is run."
  (setq eshell-previous-point (point)))

(defsubst eshell-point-within-input-p (pos)
  "Test whether POS is within an input range."
  (let (begin)
    (or (and (>= pos eshell-last-output-end)
             eshell-last-output-end)
        (and eshell-remap-previous-input
             (setq begin
                   (save-excursion
                     (eshell-bol)
                     (and (not (bolp)) (point))))
             (>= pos begin)
             (<= pos (line-end-position))
             begin))))

(defun eshell-rebind-input-map ()
  "Rebind the input keymap based on the location of the cursor."
  (ignore-errors
    (unless eshell-lock-keymap
      (if (eshell-point-within-input-p (point))
          (use-local-map eshell-input-keymap)
        (let (begin)
          (if (and eshell-confine-point-to-input
                   (setq begin
                         (eshell-point-within-input-p eshell-previous-point))
                   (memq this-command eshell-cannot-leave-input-list))
              (progn
                (use-local-map eshell-input-keymap)
                (goto-char begin)
                (if (and eshell-error-if-move-away
                         (not (eq this-command 'kill-region)))
                    (beep)))
            (use-local-map eshell-mode-map)))))))

(defun eshell-setup-input-keymap ()
  "Setup the input keymap to be used during input editing."
  (make-local-variable 'eshell-input-keymap)
  (setq eshell-input-keymap (make-sparse-keymap))
  (set-keymap-parent eshell-input-keymap eshell-mode-map)
  (let ((bindings eshell-rebind-keys-alist))
    (while bindings
      (define-key eshell-input-keymap (caar bindings)
        (cdar bindings))
      (setq bindings (cdr bindings)))))

(defun eshell-delete-backward-char (n)
  "Delete the last character, unless it's part of the output."
  (interactive "P")
  (let ((count (prefix-numeric-value n)))
    (if (eshell-point-within-input-p (- (point) count))
        (delete-backward-char count n)
      (beep))))

(defun eshell-delchar-or-maybe-eof (arg)
  "Delete ARG characters forward or send an EOF to subprocess.
Sends an EOF only if point is at the end of the buffer and there is no
input."
  (interactive "p")
  (let ((proc (eshell-interactive-process)))
    (if (eobp)
        (cond
         ((/= (point) eshell-last-output-end)
          (beep))
         (proc
          (process-send-eof))
         (t
          (eshell-life-is-too-much)))
      (eshell-delete-backward-char (- arg)))))

(provide 'em-rebind)

(require 'eshell)
(require 'esh-opt)

;;;###autoload
(progn
(defgroup eshell-script nil
  "This module allows for the execution of files containing Eshell
commands, as a script file."
  :tag "Running script files."
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-script-load-hook nil
  "A list of functions to call when loading `eshell-script'."
  :version "24.1"                       ; removed eshell-script-initialize
  :type 'hook
  :group 'eshell-script)

(defcustom eshell-login-script (expand-file-name "login" eshell-directory-name)
  "If non-nil, a file to invoke when starting up Eshell interactively.
This file should be a file containing Eshell commands, where comment
lines begin with '#'."
  :type 'file
  :group 'eshell-script)

(defcustom eshell-rc-script (expand-file-name "profile" eshell-directory-name)
  "If non-nil, a file to invoke whenever Eshell is started.
This includes when running `eshell-command'."
  :type 'file
  :group 'eshell-script)

;;; Functions:

(defun eshell-script-initialize ()
  "Initialize the script parsing code."
  (make-local-variable 'eshell-interpreter-alist)
  (setq eshell-interpreter-alist
        (cons (cons #'(lambda (file args)
                        (string= (file-name-nondirectory file)
                                 "eshell"))
                    'eshell/source)
              eshell-interpreter-alist))
  (make-local-variable 'eshell-complex-commands)
  (setq eshell-complex-commands
        (append '("source" ".") eshell-complex-commands))
  ;; these two variables are changed through usage, but we don't want
  ;; to ruin it for other modules
  (let (eshell-inside-quote-regexp
        eshell-outside-quote-regexp)
    (and (not eshell-non-interactive-p)
         eshell-login-script
         (file-readable-p eshell-login-script)
         (eshell-do-eval
          (list 'eshell-commands
                (catch 'eshell-replace-command
                  (eshell-source-file eshell-login-script))) t))
    (and eshell-rc-script
         (file-readable-p eshell-rc-script)
         (eshell-do-eval
          (list 'eshell-commands
                (catch 'eshell-replace-command
                  (eshell-source-file eshell-rc-script))) t))))

(defun eshell-source-file (file &optional args subcommand-p)
  "Execute a series of Eshell commands in FILE, passing ARGS.
Comments begin with '#'."
  (interactive "f")
  (let ((orig (point))
        (here (point-max))
        (inhibit-point-motion-hooks t))
    (goto-char (point-max))
    (with-silent-modifications
      ;; FIXME: Why not use a temporary buffer and avoid this
      ;; "insert&delete" business?  --Stef
      (insert-file-contents file)
      (goto-char (point-max))
      (throw 'eshell-replace-command
             (prog1
                 (list 'let
                       (list (list 'eshell-command-name (list 'quote file))
                             (list 'eshell-command-arguments
                                   (list 'quote args)))
                       (let ((cmd (eshell-parse-command (cons here (point)))))
                         (if subcommand-p
                             (setq cmd (list 'eshell-as-subcommand cmd)))
                         cmd))
               (delete-region here (point))
               (goto-char orig))))))

(defun eshell/source (&rest args)
  "Source a file in a subshell environment."
  (eshell-eval-using-options
   "source" args
   '((?h "help" nil nil "show this usage screen")
     :show-usage
     :usage "FILE [ARGS]
Invoke the Eshell commands in FILE in a subshell, binding ARGS to $1,
$2, etc.")
   (eshell-source-file (car args) (cdr args) t)))

(put 'eshell/source 'eshell-no-numeric-conversions t)

(defun eshell/. (&rest args)
  "Source a file in the current environment."
  (eshell-eval-using-options
   "." args
   '((?h "help" nil nil "show this usage screen")
     :show-usage
     :usage "FILE [ARGS]
Invoke the Eshell commands in FILE within the current shell
environment, binding ARGS to $1, $2, etc.")
   (eshell-source-file (car args) (cdr args))))

(put 'eshell/. 'eshell-no-numeric-conversions t)

(provide 'em-script)

(require 'esh-mode)
(eval-when-compile (require 'eshell))

;;;###autoload
(progn
(defgroup eshell-smart nil
  "This module combines the facility of normal, modern shells with
some of the edit/review concepts inherent in the design of Plan 9's
9term.  See the docs for more details.

Most likely you will have to turn this option on and play around with
it to get a real sense of how it works."
  :tag "Smart display of output"
  ;; :link '(info-link "(eshell)Smart display of output")
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-smart-load-hook nil
  "A list of functions to call when loading `eshell-smart'."
  :version "24.1"                       ; removed eshell-smart-initialize
  :type 'hook
  :group 'eshell-smart)

(defcustom eshell-smart-unload-hook
  (list
   (function
    (lambda ()
      (remove-hook 'window-configuration-change-hook
                   'eshell-refresh-windows))))
  "A hook that gets run when `eshell-smart' is unloaded."
  :type 'hook
  :group 'eshell-smart)

(defcustom eshell-review-quick-commands nil
  "If t, always review commands.
Reviewing means keeping point on the text of the command that was just
invoked, to allow corrections to be made easily.

If set to nil, quick commands won't be reviewed.  A quick command is a
command that produces no output, and exits successfully.

If set to `not-even-short-output', then the definition of \"quick
command\" is extended to include commands that produce output, if and
only if that output can be presented in its entirely in the Eshell window."
  :type '(choice (const :tag "No" nil)
                 (const :tag "Yes" t)
                 (const :tag "Not even short output"
                        not-even-short-output))
  :group 'eshell-smart)

(defcustom eshell-smart-display-navigate-list
  '(insert-parentheses
    mouse-yank-at-click
    mouse-yank-primary
    mouse-yank-secondary
    yank-pop
    yank-rectangle
    yank)
  "A list of commands which cause Eshell to jump to the end of buffer."
  :type '(repeat function)
  :group 'eshell-smart)

(defcustom eshell-smart-space-goes-to-end t
  "If non-nil, space will go to end of buffer when point-max is visible.
That is, if a command is running and the user presses SPACE at a time
when the end of the buffer is visible, point will go to the end of the
buffer and smart-display will be turned off (that is, subsequently
pressing backspace will not cause the buffer to scroll down).

This feature is provided to make it very easy to watch the output of a
long-running command, such as make, where it's more desirable to see
the output go by than to review it afterward.

Setting this variable to nil means that space and backspace will
always have a consistent behavior, which is to move back and forth
through displayed output.  But it also means that enabling output
tracking requires the user to manually move point to the end of the
buffer using \\[end-of-buffer]."
  :type 'boolean
  :group 'eshell-smart)

(defcustom eshell-where-to-jump 'begin
  "This variable indicates where point should jump to after a command.
The options are `begin', `after' or `end'."
  :type '(radio (const :tag "Beginning of command" begin)
                (const :tag "After command word" after)
                (const :tag "End of command" end))
  :group 'eshell-smart)

;;; Internal Variables:

(defvar eshell-smart-displayed nil)
(defvar eshell-smart-command-done nil)
(defvar eshell-currently-handling-window nil)

;;; Functions:

(defun eshell-smart-initialize ()
  "Setup Eshell smart display."
  (unless eshell-non-interactive-p
    ;; override a few variables, since they would interfere with the
    ;; smart display functionality.
    (set (make-local-variable 'eshell-scroll-to-bottom-on-output) nil)
    (set (make-local-variable 'eshell-scroll-to-bottom-on-input) nil)
    (set (make-local-variable 'eshell-scroll-show-maximum-output) t)

    (add-hook 'window-scroll-functions 'eshell-smart-scroll-window nil t)
    (add-hook 'window-configuration-change-hook 'eshell-refresh-windows)

    (add-hook 'eshell-output-filter-functions 'eshell-refresh-windows t t)

    (add-hook 'after-change-functions 'eshell-disable-after-change nil t)

    (add-hook 'eshell-input-filter-functions 'eshell-smart-display-setup nil t)

    (make-local-variable 'eshell-smart-command-done)
    (add-hook 'eshell-post-command-hook
              (function
               (lambda ()
                 (setq eshell-smart-command-done t))) t t)

    (unless (eq eshell-review-quick-commands t)
      (add-hook 'eshell-post-command-hook
                'eshell-smart-maybe-jump-to-end nil t))))

;; This is called by window-scroll-functions with two arguments.
(defun eshell-smart-scroll-window (wind _start)
  "Scroll the given Eshell window accordingly."
  (unless eshell-currently-handling-window
    (let ((inhibit-point-motion-hooks t)
          (eshell-currently-handling-window t))
      (save-selected-window
        (select-window wind)
        (eshell-smart-redisplay)))))

(defun eshell-refresh-windows (&optional frame)
  "Refresh all visible Eshell buffers."
  (let (affected)
    (walk-windows
     (function
      (lambda (wind)
        (with-current-buffer (window-buffer wind)
          (if eshell-mode
              (let (window-scroll-functions)
                (eshell-smart-scroll-window wind (window-start))
                (setq affected t))))))
     0 frame)
    (if affected
        (let (window-scroll-functions)
          (eshell-redisplay)))))

(defun eshell-smart-display-setup ()
  "Set the point to somewhere in the beginning of the last command."
  (cond
   ((eq eshell-where-to-jump 'begin)
    (goto-char eshell-last-input-start))
   ((eq eshell-where-to-jump 'after)
    (goto-char (next-single-property-change
                eshell-last-input-start 'arg-end))
    (if (= (point) (- eshell-last-input-end 2))
        (forward-char)))
   ((eq eshell-where-to-jump 'end)
    (goto-char (1- eshell-last-input-end)))
   (t
    (error "Invalid value for `eshell-where-to-jump'")))
  (setq eshell-smart-command-done nil)
  (add-hook 'pre-command-hook 'eshell-smart-display-move nil t)
  (eshell-refresh-windows))

;; Called from after-change-functions with 3 arguments.
(defun eshell-disable-after-change (_b _e _l)
  "Disable smart display mode if the buffer changes in any way."
  (when eshell-smart-command-done
    (remove-hook 'pre-command-hook 'eshell-smart-display-move t)
    (setq eshell-smart-command-done nil)))

(defun eshell-smart-maybe-jump-to-end ()
  "Jump to the end of the input buffer.
This is done whenever a command exits successfully and both the command
and the end of the buffer are still visible."
  (when (and (= eshell-last-command-status 0)
             (if (eq eshell-review-quick-commands 'not-even-short-output)
                 (and (pos-visible-in-window-p (point-max))
                      (pos-visible-in-window-p eshell-last-input-start))
               (= (count-lines eshell-last-input-end
                               eshell-last-output-end) 0)))
    (goto-char (point-max))
    (remove-hook 'pre-command-hook 'eshell-smart-display-move t)))

(defun eshell-smart-redisplay ()
  "Display as much output as possible, smartly."
  (if (eobp)
      (save-excursion
        (recenter -1)
        ;; trigger the redisplay now, so that we catch any attempted
        ;; point motion; this is to cover for a redisplay bug
        (eshell-redisplay))
    (let ((top-point (point)))
      (and (memq 'eshell-smart-display-move pre-command-hook)
           (>= (point) eshell-last-input-start)
           (< (point) eshell-last-input-end)
           (set-window-start (selected-window)
                             (line-beginning-position) t))
      (if (pos-visible-in-window-p (point-max))
          (save-excursion
            (goto-char (point-max))
            (recenter -1)
            (unless (pos-visible-in-window-p top-point)
              (goto-char top-point)
              (set-window-start (selected-window)
                                (line-beginning-position) t)))))))

(defun eshell-smart-goto-end ()
  "Like `end-of-buffer', but do not push a mark."
  (interactive)
  (goto-char (point-max)))

(defun eshell-smart-display-move ()
  "Handle self-inserting or movement commands intelligently."
  (let (clear)
    (if (or current-prefix-arg
            (and (> (point) eshell-last-input-start)
                 (< (point) eshell-last-input-end))
            (>= (point) eshell-last-output-end))
        (setq clear t)
      (cond
       ((eq this-command 'self-insert-command)
        (if (eq last-command-event ? )
            (if (and eshell-smart-space-goes-to-end
                     eshell-current-command)
                (if (not (pos-visible-in-window-p (point-max)))
                    (setq this-command 'scroll-up)
                  (setq this-command 'eshell-smart-goto-end))
              (setq this-command 'scroll-up))
          (setq clear t)
          (goto-char (point-max))))
       ((eq this-command 'delete-backward-char)
        (setq this-command 'ignore)
        (if (< (point) eshell-last-input-start)
            (eshell-show-output)
          (if (pos-visible-in-window-p eshell-last-input-start)
              (progn
                (ignore-errors
                  (scroll-down))
                (eshell-show-output))
            (scroll-down)
            (if (pos-visible-in-window-p eshell-last-input-end)
                (eshell-show-output)))))
       ((or (memq this-command eshell-smart-display-navigate-list)
            (and (eq this-command 'eshell-send-input)
                 (not (and (>= (point) eshell-last-input-start)
                           (< (point) eshell-last-input-end)))))
        (setq clear t)
        (goto-char (point-max)))))
    (if clear
        (remove-hook 'pre-command-hook 'eshell-smart-display-move t))))

(provide 'em-smart)

(require 'cl-lib)
(require 'esh-util)
(require 'esh-ext)
(eval-when-compile (require 'eshell))
(require 'term)

;;;###autoload
(progn
(defgroup eshell-term nil
  "This module causes visual commands (e.g., 'vi') to be executed by
the `term' package, which comes with Emacs.  This package handles most
of the ANSI control codes, allowing curses-based applications to run
within an Emacs window.  The variable `eshell-visual-commands' defines
which commands are considered visual in nature."
  :tag "Running visual commands"
  :group 'eshell-module))

;;; User Variables:

(defcustom eshell-term-load-hook nil
  "A list of functions to call when loading `eshell-term'."
  :version "24.1"                       ; removed eshell-term-initialize
  :type 'hook
  :group 'eshell-term)

(defcustom eshell-visual-commands
  '("vi"                                ; what is going on??
    "screen" "top"                      ; ok, a valid program...
    "less" "more"                       ; M-x view-file
    "lynx" "ncftp"                      ; w3.el, ange-ftp
    "pine" "tin" "trn" "elm")           ; GNUS!!
  "A list of commands that present their output in a visual fashion.

Commands listed here are run in a term buffer.

See also `eshell-visual-subcommands' and `eshell-visual-options'."
  :type '(repeat string)
  :group 'eshell-term)

(defcustom eshell-visual-subcommands
  nil
  "An alist of subcommands that present their output in a visual fashion.

An alist of the form

  ((COMMAND1 SUBCOMMAND1 SUBCOMMAND2...)
   (COMMAND2 SUBCOMMAND1 ...))

of commands with subcommands that present their output in a
visual fashion.  A likely entry is

  (\"git\" \"log\" \"diff\" \"show\")

because git shows logs and diffs using a pager by default.

See also `eshell-visual-commands' and `eshell-visual-options'."
  :type '(repeat (cons (string :tag "Command")
                       (repeat (string :tag "Subcommand"))))
  :version "24.4"
  :group 'eshell-term)

(defcustom eshell-visual-options
  nil
  "An alist of the form

  ((COMMAND1 OPTION1 OPTION2...)
   (COMMAND2 OPTION1 ...))

of commands with options that present their output in a visual
fashion.  For example, a sensible entry would be

  (\"git\" \"--help\")

because \"git <command> --help\" shows the command's
documentation with a pager.

See also `eshell-visual-commands' and `eshell-visual-subcommands'."
  :type '(repeat (cons (string :tag "Command")
                       (repeat (string :tag "Option"))))
  :version "24.4"
  :group 'eshell-term)

;; If you change this from term-term-name, you need to ensure that the
;; value you choose exists in the system's terminfo database.  (Bug#12485)
(defcustom eshell-term-name term-term-name
  "Name to use for the TERM variable when running visual commands.
See `term-term-name' in term.el for more information on how this is
used."
  :version "24.3"              ; eterm -> term-term-name = eterm-color
  :type 'string
  :group 'eshell-term)

(defcustom eshell-escape-control-x t
  "If non-nil, allow <C-x> to be handled by Emacs key in visual buffers.
See the variables `eshell-visual-commands',
`eshell-visual-subcommands', and `eshell-visual-options'.  If
this variable is set to nil, <C-x> will send that control
character to the invoked process."
  :type 'boolean
  :group 'eshell-term)

;;; Internal Variables:

(defvar eshell-parent-buffer)

;;; Functions:

(defun eshell-term-initialize ()
  "Initialize the `term' interface code."
  (make-local-variable 'eshell-interpreter-alist)
  (setq eshell-interpreter-alist
        (cons (cons #'eshell-visual-command-p
                    'eshell-exec-visual)
              eshell-interpreter-alist)))

(defun eshell-visual-command-p (command args)
  "Returns non-nil when given a visual command.
If either COMMAND or a subcommand in ARGS (e.g. git log) is a
visual command, returns non-nil."
  (let ((command (file-name-nondirectory command)))
    (and (eshell-interactive-output-p)
         (or (member command eshell-visual-commands)
             (member (car args)
                     (cdr (assoc command eshell-visual-subcommands)))
             (cl-intersection args
                              (cdr (assoc command eshell-visual-options))
                              :test 'string=)))))

(defun eshell-exec-visual (&rest args)
  "Run the specified PROGRAM in a terminal emulation buffer.
ARGS are passed to the program.  At the moment, no piping of input is
allowed."
  (let* (eshell-interpreter-alist
         (interp (eshell-find-interpreter (car args) (cdr args)))
         (program (car interp))
         (args (eshell-flatten-list
                (eshell-stringify-list (append (cdr interp)
                                               (cdr args)))))
         (term-buf
          (generate-new-buffer
           (concat "*" (file-name-nondirectory program) "*")))
         (eshell-buf (current-buffer)))
    (save-current-buffer
      (switch-to-buffer term-buf)
      (term-mode)
      (set (make-local-variable 'term-term-name) eshell-term-name)
      (make-local-variable 'eshell-parent-buffer)
      (setq eshell-parent-buffer eshell-buf)
      (term-exec term-buf program program nil args)
      (let ((proc (get-buffer-process term-buf)))
        (if (and proc (eq 'run (process-status proc)))
            (set-process-sentinel proc 'eshell-term-sentinel)
          (error "Failed to invoke visual command")))
      (term-char-mode)
      (if eshell-escape-control-x
          (term-set-escape-char ?\C-x))))
  nil)

;; Process sentinels receive two arguments.
(defun eshell-term-sentinel (proc _string)
  "Destroy the buffer visiting PROC."
  (let ((proc-buf (process-buffer proc)))
    (when (and proc-buf (buffer-live-p proc-buf)
               (not (eq 'run (process-status proc)))
               (= (process-exit-status proc) 0))
      (if (eq (current-buffer) proc-buf)
          (let ((buf (and (boundp 'eshell-parent-buffer)
                          eshell-parent-buffer
                          (buffer-live-p eshell-parent-buffer)
                          eshell-parent-buffer)))
            (if buf
                (switch-to-buffer buf))))
      (kill-buffer proc-buf))))

;; jww (1999-09-17): The code below will allow Eshell to send input
;; characters directly to the currently running interactive process.
;; However, since this would introduce other problems that would need
;; solutions, I'm going to let it wait until after 2.1.

;; (defvar eshell-term-raw-map nil
;;   "Keyboard map for sending characters directly to the inferior process.")
;; (defvar eshell-term-escape-char nil
;;   "Escape character for char-sub-mode of term mode.
;; Do not change it directly;  use term-set-escape-char instead.")
;; (defvar eshell-term-raw-escape-map nil)

;; (defun eshell-term-send-raw-string (chars)
;;   (goto-char eshell-last-output-end)
;;   (process-send-string (eshell-interactive-process) chars))

;; (defun eshell-term-send-raw ()
;;   "Send the last character typed through the terminal-emulator
;; without any interpretation."
;;   (interactive)
;;   ;; Convert `return' to C-m, etc.
;;   (if (and (symbolp last-input-event)
;;          (get last-input-event 'ascii-character))
;;       (setq last-input-event (get last-input-event 'ascii-character)))
;;   (eshell-term-send-raw-string (make-string 1 last-input-event)))

;; (defun eshell-term-send-raw-meta ()
;;   (interactive)
;;   (if (symbolp last-input-event)
;;       ;; Convert `return' to C-m, etc.
;;       (let ((tmp (get last-input-event 'event-symbol-elements)))
;;       (if tmp
;;           (setq last-input-event (car tmp)))
;;       (if (symbolp last-input-event)
;;           (progn
;;             (setq tmp (get last-input-event 'ascii-character))
;;             (if tmp (setq last-input-event tmp))))))
;;   (eshell-term-send-raw-string (if (and (numberp last-input-event)
;;                                       (> last-input-event 127)
;;                                       (< last-input-event 256))
;;                                  (make-string 1 last-input-event)
;;                                (format "\e%c" last-input-event))))

;; (defun eshell-term-mouse-paste (click arg)
;;   "Insert the last stretch of killed text at the position clicked on."
;;   (interactive "e\nP")
;;   (if (boundp 'xemacs-logo)
;;       (eshell-term-send-raw-string
;;        (or (condition-case () (x-get-selection) (error ()))
;;          (error "No selection available")))
;;     ;; Give temporary modes such as isearch a chance to turn off.
;;     (run-hooks 'mouse-leave-buffer-hook)
;;     (setq this-command 'yank)
;;     (eshell-term-send-raw-string
;;      (current-kill (cond ((listp arg) 0)
;;                        ((eq arg '-) -1)
;;                        (t (1- arg)))))))

;; ;; Which would be better:  "\e[A" or "\eOA"? readline accepts either.
;; ;; For my configuration it's definitely better \eOA but YMMV. -mm
;; ;; For example: vi works with \eOA while elm wants \e[A ...
;; (defun eshell-term-send-up    () (interactive) (eshell-term-send-raw-string "\eOA"))
;; (defun eshell-term-send-down  () (interactive) (eshell-term-send-raw-string "\eOB"))
;; (defun eshell-term-send-right () (interactive) (eshell-term-send-raw-string "\eOC"))
;; (defun eshell-term-send-left  () (interactive) (eshell-term-send-raw-string "\eOD"))
;; (defun eshell-term-send-home  () (interactive) (eshell-term-send-raw-string "\e[1~"))
;; (defun eshell-term-send-end   () (interactive) (eshell-term-send-raw-string "\e[4~"))
;; (defun eshell-term-send-prior () (interactive) (eshell-term-send-raw-string "\e[5~"))
;; (defun eshell-term-send-next  () (interactive) (eshell-term-send-raw-string "\e[6~"))
;; (defun eshell-term-send-del   () (interactive) (eshell-term-send-raw-string "\C-?"))
;; (defun eshell-term-send-backspace  () (interactive) (eshell-term-send-raw-string "\C-H"))

;; (defun eshell-term-set-escape-char (c)
;;   "Change term-escape-char and keymaps that depend on it."
;;   (if eshell-term-escape-char
;;       (define-key eshell-term-raw-map eshell-term-escape-char 'eshell-term-send-raw))
;;   (setq c (make-string 1 c))
;;   (define-key eshell-term-raw-map c eshell-term-raw-escape-map)
;;   ;; Define standard bindings in eshell-term-raw-escape-map
;;   (define-key eshell-term-raw-escape-map "\C-x"
;;     (lookup-key (current-global-map) "\C-x"))
;;   (define-key eshell-term-raw-escape-map "\C-v"
;;     (lookup-key (current-global-map) "\C-v"))
;;   (define-key eshell-term-raw-escape-map "\C-u"
;;     (lookup-key (current-global-map) "\C-u"))
;;   (define-key eshell-term-raw-escape-map c 'eshell-term-send-raw))

;; (defun eshell-term-char-mode ()
;;   "Switch to char (\"raw\") sub-mode of term mode.
;; Each character you type is sent directly to the inferior without
;; intervention from Emacs, except for the escape character (usually C-c)."
;;   (interactive)
;;   (if (not eshell-term-raw-map)
;;       (let* ((map (make-keymap))
;;            (esc-map (make-keymap))
;;            (i 0))
;;       (while (< i 128)
;;         (define-key map (make-string 1 i) 'eshell-term-send-raw)
;;         (define-key esc-map (make-string 1 i) 'eshell-term-send-raw-meta)
;;         (setq i (1+ i)))
;;       (define-key map "\e" esc-map)
;;       (setq eshell-term-raw-map map)
;;       (setq eshell-term-raw-escape-map
;;             (copy-keymap (lookup-key (current-global-map) "\C-x")))
;;       (if (boundp 'xemacs-logo)
;;           (define-key eshell-term-raw-map [button2] 'eshell-term-mouse-paste)
;;         (define-key eshell-term-raw-map [mouse-2] 'eshell-term-mouse-paste))
;;       (define-key eshell-term-raw-map [up] 'eshell-term-send-up)
;;       (define-key eshell-term-raw-map [down] 'eshell-term-send-down)
;;       (define-key eshell-term-raw-map [right] 'eshell-term-send-right)
;;       (define-key eshell-term-raw-map [left] 'eshell-term-send-left)
;;       (define-key eshell-term-raw-map [delete] 'eshell-term-send-del)
;;       (define-key eshell-term-raw-map [backspace] 'eshell-term-send-backspace)
;;       (define-key eshell-term-raw-map [home] 'eshell-term-send-home)
;;       (define-key eshell-term-raw-map [end] 'eshell-term-send-end)
;;       (define-key eshell-term-raw-map [prior] 'eshell-term-send-prior)
;;       (define-key eshell-term-raw-map [next] 'eshell-term-send-next)
;;       (eshell-term-set-escape-char ?\C-c))))

;; (defun eshell-term-line-mode  ()
;;   "Switch to line (\"cooked\") sub-mode of eshell-term mode."
;;  (use-local-map term-old-mode-map))

(provide 'em-term)

(require 'eshell)
(require 'esh-opt)
(require 'pcomplete)

;;;###autoload
(progn
(defgroup eshell-unix nil
  "This module defines many of the more common UNIX utilities as
aliases implemented in Lisp.  These include mv, ln, cp, rm, etc.  If
the user passes arguments which are too complex, or are unrecognized
by the Lisp variant, the external version will be called (if
available).  The only reason not to use them would be because they are
usually much slower.  But in several cases their tight integration
with Eshell makes them more versatile than their traditional cousins
\(such as being able to use `kill' to kill Eshell background processes
by name)."
  :tag "UNIX commands in Lisp"
  :group 'eshell-module))

(defcustom eshell-unix-load-hook nil
  "A list of functions to run when `eshell-unix' is loaded."
  :version "24.1"                       ; removed eshell-unix-initialize
  :type 'hook
  :group 'eshell-unix)

(defcustom eshell-plain-grep-behavior nil
  "If non-nil, standalone \"grep\" commands will behave normally.
Standalone in this context means not redirected, and not on the
receiving side of a command pipeline."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-no-grep-available (not (eshell-search-path "grep"))
  "If non-nil, no grep is available on the current machine."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-plain-diff-behavior nil
  "If non-nil, standalone \"diff\" commands will behave normally.
Standalone in this context means not redirected, and not on the
receiving side of a command pipeline."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-plain-locate-behavior (featurep 'xemacs)
  "If non-nil, standalone \"locate\" commands will behave normally.
Standalone in this context means not redirected, and not on the
receiving side of a command pipeline."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-rm-removes-directories nil
  "If non-nil, `rm' will remove directory entries.
Otherwise, `rmdir' is required."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-rm-interactive-query (= (user-uid) 0)
  "If non-nil, `rm' will query before removing anything."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-mv-interactive-query (= (user-uid) 0)
  "If non-nil, `mv' will query before overwriting anything."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-mv-overwrite-files t
  "If non-nil, `mv' will overwrite files without warning."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-cp-interactive-query (= (user-uid) 0)
  "If non-nil, `cp' will query before overwriting anything."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-cp-overwrite-files t
  "If non-nil, `cp' will overwrite files without warning."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-ln-interactive-query (= (user-uid) 0)
  "If non-nil, `ln' will query before overwriting anything."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-ln-overwrite-files nil
  "If non-nil, `ln' will overwrite files without warning."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-default-target-is-dot nil
  "If non-nil, the default destination for cp, mv or ln is `.'."
  :type 'boolean
  :group 'eshell-unix)

(defcustom eshell-du-prefer-over-ange nil
  "Use Eshell's du in ange-ftp remote directories.
Otherwise, Emacs will attempt to use rsh to invoke du on the remote machine."
  :type 'boolean
  :group 'eshell-unix)

;;; Functions:

(defun eshell-unix-initialize ()
  "Initialize the UNIX support/emulation code."
  (when (eshell-using-module 'eshell-cmpl)
    (add-hook 'pcomplete-try-first-hook
              'eshell-complete-host-reference nil t))
  (make-local-variable 'eshell-complex-commands)
  (setq eshell-complex-commands
        (append '("grep" "egrep" "fgrep" "agrep" "glimpse" "locate"
                  "cat" "time" "cp" "mv" "make" "du" "diff")
                eshell-complex-commands)))

(defalias 'eshell/date     'current-time-string)
(defalias 'eshell/basename 'file-name-nondirectory)
(defalias 'eshell/dirname  'file-name-directory)

(defvar em-interactive)
(defvar em-preview)
(defvar em-recursive)
(defvar em-verbose)

(defun eshell/man (&rest args)
  "Invoke man, flattening the arguments appropriately."
  (funcall 'man (apply 'eshell-flatten-and-stringify args)))

(put 'eshell/man 'eshell-no-numeric-conversions t)

(defun eshell/info (&rest args)
  "Run the info command in-frame with the same behavior as command-line `info', ie:
  'info'           => goes to top info window
  'info arg1'      => IF arg1 is a file, then visits arg1
  'info arg1'      => OTHERWISE goes to top info window and then menu item arg1
  'info arg1 arg2' => does action for arg1 (either visit-file or menu-item) and then menu item arg2
  etc."
  (eval-and-compile (require 'info))
  (let ((file (cond
                ((not (stringp (car args)))
                 nil)
                ((file-exists-p (expand-file-name (car args)))
                 (expand-file-name (car args)))
                ((file-exists-p (concat (expand-file-name (car args)) ".info"))
                 (concat (expand-file-name (car args)) ".info")))))

    ;; If the first arg is a file, then go to that file's Top node
    ;; Otherwise, go to the global directory
    (if file
      (progn
        (setq args (cdr args))
        (Info-find-node file "Top"))
      (Info-directory))

    ;; Treat all remaining args as menu references
    (while args
      (Info-menu (car args))
      (setq args (cdr args)))))

(defun eshell-remove-entries (files &optional toplevel)
  "Remove all of the given FILES, perhaps interactively."
  (while files
    (if (string-match "\\`\\.\\.?\\'"
                      (file-name-nondirectory (car files)))
        (if toplevel
            (eshell-error "rm: cannot remove `.' or `..'\n"))
      (if (and (file-directory-p (car files))
               (not (file-symlink-p (car files))))
          (progn
            (if em-verbose
                (eshell-printn (format "rm: removing directory `%s'"
                                       (car files))))
            (unless
                (or em-preview
                    (and em-interactive
                         (not (y-or-n-p
                               (format "rm: remove directory `%s'? "
                                       (car files))))))
              (eshell-funcalln 'delete-directory (car files) t t)))
        (if em-verbose
            (eshell-printn (format "rm: removing file `%s'"
                                   (car files))))
        (unless (or em-preview
                    (and em-interactive
                         (not (y-or-n-p
                               (format "rm: remove `%s'? "
                                       (car files))))))
          (eshell-funcalln 'delete-file (car files) t))))
    (setq files (cdr files))))

(defun eshell/rm (&rest args)
  "Implementation of rm in Lisp.
This is implemented to call either `delete-file', `kill-buffer',
`kill-process', or `unintern', depending on the nature of the
argument."
  (setq args (eshell-flatten-list args))
  (eshell-eval-using-options
   "rm" args
   '((?h "help" nil nil "show this usage screen")
     (?f "force" nil force-removal "force removal")
     (?i "interactive" nil em-interactive "prompt before any removal")
     (?n "preview" nil em-preview "don't change anything on disk")
     (?r "recursive" nil em-recursive
         "remove the contents of directories recursively")
     (?R nil nil em-recursive "(same)")
     (?v "verbose" nil em-verbose "explain what is being done")
     :preserve-args
     :external "rm"
     :show-usage
     :usage "[OPTION]... FILE...
Remove (unlink) the FILE(s).")
   (unless em-interactive
     (setq em-interactive eshell-rm-interactive-query))
   (if (and force-removal em-interactive)
       (setq em-interactive nil))
   (while args
     (let ((entry (if (stringp (car args))
                      (directory-file-name (car args))
                    (if (numberp (car args))
                        (number-to-string (car args))
                      (car args)))))
       (cond
        ((bufferp entry)
         (if em-verbose
             (eshell-printn (format "rm: removing buffer `%s'" entry)))
         (unless (or em-preview
                     (and em-interactive
                          (not (y-or-n-p (format "rm: delete buffer `%s'? "
                                                 entry)))))
           (eshell-funcalln 'kill-buffer entry)))
        ((eshell-processp entry)
         (if em-verbose
             (eshell-printn (format "rm: killing process `%s'" entry)))
         (unless (or em-preview
                     (and em-interactive
                          (not (y-or-n-p (format "rm: kill process `%s'? "
                                                 entry)))))
           (eshell-funcalln 'kill-process entry)))
        ((symbolp entry)
         (if em-verbose
             (eshell-printn (format "rm: uninterning symbol `%s'" entry)))
         (unless
             (or em-preview
                 (and em-interactive
                      (not (y-or-n-p (format "rm: unintern symbol `%s'? "
                                             entry)))))
           (eshell-funcalln 'unintern entry)))
        ((stringp entry)
         ;; -f should silently ignore missing files (bug#15373).
         (unless (and force-removal
                      (not (file-exists-p entry)))
           (if (and (file-directory-p entry)
                    (not (file-symlink-p entry)))
               (if (or em-recursive
                       eshell-rm-removes-directories)
                   (if (or em-preview
                           (not em-interactive)
                           (y-or-n-p
                            (format "rm: descend into directory `%s'? "
                                    entry)))
                     (eshell-remove-entries (list entry) t))
                 (eshell-error (format "rm: %s: is a directory\n" entry)))
             (eshell-remove-entries (list entry) t))))))
     (setq args (cdr args)))
   nil))

(put 'eshell/rm 'eshell-no-numeric-conversions t)

(defun eshell/mkdir (&rest args)
  "Implementation of mkdir in Lisp."
  (eshell-eval-using-options
   "mkdir" args
   '((?h "help" nil nil "show this usage screen")
     (?p "parents" nil em-parents "make parent directories as needed")
     :external "mkdir"
     :show-usage
     :usage "[OPTION] DIRECTORY...
Create the DIRECTORY(ies), if they do not already exist.")
   (while args
     (eshell-funcalln 'make-directory (car args) em-parents)
     (setq args (cdr args)))
   nil))

(put 'eshell/mkdir 'eshell-no-numeric-conversions t)

(defun eshell/rmdir (&rest args)
  "Implementation of rmdir in Lisp."
  (eshell-eval-using-options
   "rmdir" args
   '((?h "help" nil nil "show this usage screen")
     :external "rmdir"
     :show-usage
     :usage "[OPTION] DIRECTORY...
Remove the DIRECTORY(ies), if they are empty.")
   (while args
     (eshell-funcalln 'delete-directory (car args))
     (setq args (cdr args)))
   nil))

(put 'eshell/rmdir 'eshell-no-numeric-conversions t)

(defvar no-dereference)

(defvar eshell-warn-dot-directories t)

(defun eshell-shuffle-files (command action files target func deep &rest args)
  "Shuffle around some filesystem entries, using FUNC to do the work."
  (let ((attr-target (eshell-file-attributes target))
        (is-dir (or (file-directory-p target)
                    (and em-preview (not eshell-warn-dot-directories))))
        attr)
    (if (and (not em-preview) (not is-dir)
             (> (length files) 1))
        (error "%s: when %s multiple files, last argument must be a directory"
               command action))
    (while files
      (setcar files (directory-file-name (car files)))
      (cond
       ((string-match "\\`\\.\\.?\\'"
                      (file-name-nondirectory (car files)))
        (if eshell-warn-dot-directories
            (eshell-error (format "%s: %s: omitting directory\n"
                                  command (car files)))))
       ((and attr-target
             (or (not (eshell-under-windows-p))
                 (eq system-type 'ms-dos))
             (setq attr (eshell-file-attributes (car files)))
             (nth 10 attr-target) (nth 10 attr)
             ;; Use equal, not -, since the inode and the device could
             ;; cons cells.
             (equal (nth 10 attr-target) (nth 10 attr))
             (nth 11 attr-target) (nth 11 attr)
             (equal (nth 11 attr-target) (nth 11 attr)))
        (eshell-error (format "%s: `%s' and `%s' are the same file\n"
                              command (car files) target)))
       (t
        (let ((source (car files))
              (target (if is-dir
                          (expand-file-name
                           (file-name-nondirectory (car files)) target)
                        target))
              link)
          (if (and (file-directory-p source)
                   (or (not no-dereference)
                       (not (file-symlink-p source)))
                   (not (memq func '(make-symbolic-link
                                     add-name-to-file))))
              (if (and (eq func 'copy-file)
                       (not em-recursive))
                  (eshell-error (format "%s: %s: omitting directory\n"
                                        command (car files)))
                (let (eshell-warn-dot-directories)
                  (if (and (not deep)
                           (eq func 'rename-file)
                           ;; Use equal, since the device might be a
                           ;; cons cell.
                           (equal (nth 11 (eshell-file-attributes
                                           (file-name-directory
                                            (directory-file-name
                                             (expand-file-name source)))))
                                  (nth 11 (eshell-file-attributes
                                           (file-name-directory
                                            (directory-file-name
                                             (expand-file-name target)))))))
                      (apply 'eshell-funcalln func source target args)
                  (unless (file-directory-p target)
                    (if em-verbose
                        (eshell-printn
                         (format "%s: making directory %s"
                                 command target)))
                    (unless em-preview
                      (eshell-funcalln 'make-directory target)))
                  (apply 'eshell-shuffle-files
                         command action
                         (mapcar
                          (function
                           (lambda (file)
                             (concat source "/" file)))
                          (directory-files source))
                         target func t args)
                  (when (eq func 'rename-file)
                    (if em-verbose
                        (eshell-printn
                         (format "%s: deleting directory %s"
                                 command source)))
                    (unless em-preview
                      (eshell-funcalln 'delete-directory source))))))
            (if em-verbose
                (eshell-printn (format "%s: %s -> %s" command
                                       source target)))
            (unless em-preview
              (if (and no-dereference
                       (setq link (file-symlink-p source)))
                  (progn
                    (apply 'eshell-funcalln 'make-symbolic-link
                           link target args)
                    (if (eq func 'rename-file)
                        (if (and (file-directory-p source)
                                 (not (file-symlink-p source)))
                            (eshell-funcalln 'delete-directory source)
                          (eshell-funcalln 'delete-file source))))
                (apply 'eshell-funcalln func source target args)))))))
      (setq files (cdr files)))))

(defun eshell-shorthand-tar-command (command args)
  "Rewrite `cp -v dir a.tar.gz' to `tar cvzf a.tar.gz dir'."
  (let* ((archive (car (last args)))
         (tar-args
          (cond ((string-match "z2" archive) "If")
                ((string-match "gz" archive) "zf")
                ((string-match "\\(az\\|Z\\)" archive) "Zf")
                (t "f"))))
    (if (file-exists-p archive)
        (setq tar-args (concat "u" tar-args))
      (setq tar-args (concat "c" tar-args)))
    (if em-verbose
        (setq tar-args (concat "v" tar-args)))
    (if (equal command "mv")
        (setq tar-args (concat "--remove-files -" tar-args)))
    ;; truncate the archive name from the arguments
    (setcdr (last args 2) nil)
    (throw 'eshell-replace-command
           (eshell-parse-command
            (format "tar %s %s" tar-args archive) args))))

(defvar ange-cache)                     ; XEmacs?  See esh-util

;; this is to avoid duplicating code...
(defmacro eshell-mvcpln-template (command action func query-var
                                          force-var &optional preserve)
  `(let ((len (length args)))
     (if (or (= len 0)
             (and (= len 1) (null eshell-default-target-is-dot)))
         (error "%s: missing destination file or directory" ,command))
     (if (= len 1)
         (nconc args '(".")))
     (setq args (eshell-stringify-list (eshell-flatten-list args)))
     (if (and ,(not (equal command "ln"))
              (string-match eshell-tar-regexp (car (last args)))
              (or (> (length args) 2)
                  (and (file-directory-p (car args))
                       (or (not no-dereference)
                           (not (file-symlink-p (car args)))))))
         (eshell-shorthand-tar-command ,command args)
       (let ((target (car (last args)))
             ange-cache)
         (setcdr (last args 2) nil)
         (eshell-shuffle-files
          ,command ,action args target ,func nil
          ,@(append
             `((if (and (or em-interactive
                            ,query-var)
                        (not force))
                   1 (or force ,force-var)))
             (if preserve
                 (list preserve)))))
       nil)))

(defun eshell/mv (&rest args)
  "Implementation of mv in Lisp."
  (eshell-eval-using-options
   "mv" args
   '((?f "force" nil force
         "remove existing destinations, never prompt")
     (?i "interactive" nil em-interactive
         "request confirmation if target already exists")
     (?n "preview" nil em-preview
         "don't change anything on disk")
     (?v "verbose" nil em-verbose
         "explain what is being done")
     (nil "help" nil nil "show this usage screen")
     :preserve-args
     :external "mv"
     :show-usage
     :usage "[OPTION]... SOURCE DEST
   or: mv [OPTION]... SOURCE... DIRECTORY
Rename SOURCE to DEST, or move SOURCE(s) to DIRECTORY.
\[OPTION] DIRECTORY...")
   (let ((no-dereference t))
     (eshell-mvcpln-template "mv" "moving" 'rename-file
                             eshell-mv-interactive-query
                             eshell-mv-overwrite-files))))

(put 'eshell/mv 'eshell-no-numeric-conversions t)

(defun eshell/cp (&rest args)
  "Implementation of cp in Lisp."
  (eshell-eval-using-options
   "cp" args
   '((?a "archive" nil archive
         "same as -dpR")
     (?d "no-dereference" nil no-dereference
         "preserve links")
     (?f "force" nil force
         "remove existing destinations, never prompt")
     (?i "interactive" nil em-interactive
         "request confirmation if target already exists")
     (?n "preview" nil em-preview
         "don't change anything on disk")
     (?p "preserve" nil preserve
         "preserve file attributes if possible")
     (?r "recursive" nil em-recursive
         "copy directories recursively")
     (?R nil nil em-recursive
         "as for -r")
     (?v "verbose" nil em-verbose
         "explain what is being done")
     (nil "help" nil nil "show this usage screen")
     :preserve-args
     :external "cp"
     :show-usage
     :usage "[OPTION]... SOURCE DEST
   or:  cp [OPTION]... SOURCE... DIRECTORY
Copy SOURCE to DEST, or multiple SOURCE(s) to DIRECTORY.")
   (if archive
       (setq preserve t no-dereference t em-recursive t))
   (eshell-mvcpln-template "cp" "copying" 'copy-file
                           eshell-cp-interactive-query
                           eshell-cp-overwrite-files preserve)))

(put 'eshell/cp 'eshell-no-numeric-conversions t)

(defun eshell/ln (&rest args)
  "Implementation of ln in Lisp."
  (eshell-eval-using-options
   "ln" args
   '((?h "help" nil nil "show this usage screen")
     (?s "symbolic" nil symbolic
         "make symbolic links instead of hard links")
     (?i "interactive" nil em-interactive
         "request confirmation if target already exists")
     (?f "force" nil force "remove existing destinations, never prompt")
     (?n "preview" nil em-preview
         "don't change anything on disk")
     (?v "verbose" nil em-verbose "explain what is being done")
     :preserve-args
     :external "ln"
     :show-usage
     :usage "[OPTION]... TARGET [LINK_NAME]
   or:  ln [OPTION]... TARGET... DIRECTORY
Create a link to the specified TARGET with optional LINK_NAME.  If there is
more than one TARGET, the last argument must be a directory;  create links
in DIRECTORY to each TARGET.  Create hard links by default, symbolic links
with '--symbolic'.  When creating hard links, each TARGET must exist.")
   (let ((no-dereference t))
     (eshell-mvcpln-template "ln" "linking"
                             (if symbolic
                                 'make-symbolic-link
                               'add-name-to-file)
                             eshell-ln-interactive-query
                             eshell-ln-overwrite-files))))

(put 'eshell/ln 'eshell-no-numeric-conversions t)

(defun eshell/cat (&rest args)
  "Implementation of cat in Lisp.
If in a pipeline, or the file is not a regular file, directory or
symlink, then revert to the system's definition of cat."
  (setq args (eshell-stringify-list (eshell-flatten-list args)))
  (if (or eshell-in-pipeline-p
          (catch 'special
            (dolist (arg args)
              (unless (or (and (stringp arg)
                               (> (length arg) 0)
                               (eq (aref arg 0) ?-))
                          (let ((attrs (eshell-file-attributes arg)))
                            (and attrs (memq (aref (nth 8 attrs) 0)
                                             '(?d ?l ?-)))))
                (throw 'special t)))))
      (let ((ext-cat (eshell-search-path "cat")))
        (if ext-cat
            (throw 'eshell-replace-command
                   (eshell-parse-command (eshell-quote-argument ext-cat) args))
          (if eshell-in-pipeline-p
              (error "Eshell's `cat' does not work in pipelines")
            (error "Eshell's `cat' cannot display one of the files given"))))
    (eshell-init-print-buffer)
    (eshell-eval-using-options
     "cat" args
     '((?h "help" nil nil "show this usage screen")
       :external "cat"
       :show-usage
       :usage "[OPTION] FILE...
Concatenate FILE(s), or standard input, to standard output.")
     (dolist (file args)
       (if (string= file "-")
           (throw 'eshell-external
                  (eshell-external-command "cat" args))))
     (let ((curbuf (current-buffer)))
       (dolist (file args)
         (with-temp-buffer
           (insert-file-contents file)
           (goto-char (point-min))
           (while (not (eobp))
             (let ((str (buffer-substring
                         (point) (min (1+ (line-end-position))
                                      (point-max)))))
               (with-current-buffer curbuf
                 (eshell-buffered-print str)))
             (forward-line)))))
     (eshell-flush)
     ;; if the file does not end in a newline, do not emit one
     (setq eshell-ensure-newline-p nil))))

(put 'eshell/cat 'eshell-no-numeric-conversions t)

;; special front-end functions for compilation-mode buffers

(defun eshell/make (&rest args)
  "Use `compile' to do background makes."
  (if (and eshell-current-subjob-p
           (eshell-interactive-output-p))
      (let ((compilation-process-setup-function
             (list 'lambda nil
                   (list 'setq 'process-environment
                         (list 'quote (eshell-copy-environment))))))
        (compile (concat "make " (eshell-flatten-and-stringify args))))
    (throw 'eshell-replace-command
           (eshell-parse-command "*make" (eshell-stringify-list
                                          (eshell-flatten-list args))))))

(put 'eshell/make 'eshell-no-numeric-conversions t)

(defun eshell-occur-mode-goto-occurrence ()
  "Go to the occurrence the current line describes."
  (interactive)
  (let ((pos (occur-mode-find-occurrence)))
    (pop-to-buffer (marker-buffer pos))
    (goto-char (marker-position pos))))

(defun eshell-occur-mode-mouse-goto (event)
  "In Occur mode, go to the occurrence whose line you click on."
  (interactive "e")
  (let (pos)
    (with-current-buffer (window-buffer (posn-window (event-end event)))
      (save-excursion
        (goto-char (posn-point (event-end event)))
        (setq pos (occur-mode-find-occurrence))))
    (pop-to-buffer (marker-buffer pos))
    (goto-char (marker-position pos))))

(defun eshell-poor-mans-grep (args)
  "A poor version of grep that opens every file and uses `occur'.
This eats up memory, since it leaves the buffers open (to speed future
searches), and it's very slow.  But, if your system has no grep
available..."
  (save-selected-window
    (let ((default-dir default-directory))
      (with-current-buffer (get-buffer-create "*grep*")
        (let ((inhibit-read-only t)
              (default-directory default-dir))
          (erase-buffer)
          (occur-mode)
          (let ((files (eshell-stringify-list
                        (eshell-flatten-list (cdr args))))
                (inhibit-redisplay t)
                string)
            (when (car args)
              (if (get-buffer "*Occur*")
                  (kill-buffer (get-buffer "*Occur*")))
              (setq string nil)
              (while files
                (with-current-buffer (find-file-noselect (car files))
                  (save-excursion
                    (ignore-errors
                      (occur (car args))))
                  (if (get-buffer "*Occur*")
                      (with-current-buffer (get-buffer "*Occur*")
                        (setq string (buffer-string))
                        (kill-buffer (current-buffer)))))
                (if string (insert string))
                (setq string nil
                      files (cdr files)))))
          (local-set-key [mouse-2] 'eshell-occur-mode-mouse-goto)
          (local-set-key [(control ?c) (control ?c)]
                         'eshell-occur-mode-goto-occurrence)
          (local-set-key [(control ?m)]
                         'eshell-occur-mode-goto-occurrence)
          (local-set-key [return] 'eshell-occur-mode-goto-occurrence)
          (pop-to-buffer (current-buffer) t)
          (goto-char (point-min))
          (resize-temp-buffer-window))))))

(defvar compilation-scroll-output)

(defun eshell-grep (command args &optional maybe-use-occur)
  "Generic service function for the various grep aliases.
It calls Emacs's grep utility if the command is not redirecting output,
and if it's not part of a command pipeline.  Otherwise, it calls the
external command."
  (if (and maybe-use-occur eshell-no-grep-available)
      (eshell-poor-mans-grep args)
    (if (or eshell-plain-grep-behavior
            (not (and (eshell-interactive-output-p)
                      (not eshell-in-pipeline-p)
                      (not eshell-in-subcommand-p))))
        (throw 'eshell-replace-command
               (eshell-parse-command (concat "*" command)
                                     (eshell-stringify-list
                                      (eshell-flatten-list args))))
      (let* ((args (mapconcat 'identity
                              (mapcar 'shell-quote-argument
                                      (eshell-stringify-list
                                       (eshell-flatten-list args)))
                              " "))
             (cmd (progn
                    (set-text-properties 0 (length args)
                                         '(invisible t) args)
                    (format "%s -n %s" command args)))
             compilation-scroll-output)
        (grep cmd)))))

(defun eshell/grep (&rest args)
  "Use Emacs grep facility instead of calling external grep."
  (eshell-grep "grep" args t))

(defun eshell/egrep (&rest args)
  "Use Emacs grep facility instead of calling external egrep."
  (eshell-grep "egrep" args t))

(defun eshell/fgrep (&rest args)
  "Use Emacs grep facility instead of calling external fgrep."
  (eshell-grep "fgrep" args t))

(defun eshell/agrep (&rest args)
  "Use Emacs grep facility instead of calling external agrep."
  (eshell-grep "agrep" args))

(defun eshell/glimpse (&rest args)
  "Use Emacs grep facility instead of calling external glimpse."
  (let (null-device)
    (eshell-grep "glimpse" (append '("-z" "-y") args))))

;; completions rules for some common UNIX commands

(defsubst eshell-complete-hostname ()
  "Complete a command that wants a hostname for an argument."
  (pcomplete-here (eshell-read-host-names)))

(defun eshell-complete-host-reference ()
  "If there is a host reference, complete it."
  (let ((arg (pcomplete-actual-arg))
        index)
    (when (setq index (string-match "@[a-z.]*\\'" arg))
      (setq pcomplete-stub (substring arg (1+ index))
            pcomplete-last-completion-raw t)
      (throw 'pcomplete-completions (eshell-read-host-names)))))

(defalias 'pcomplete/ftp    'eshell-complete-hostname)
(defalias 'pcomplete/ncftp  'eshell-complete-hostname)
(defalias 'pcomplete/ping   'eshell-complete-hostname)
(defalias 'pcomplete/rlogin 'eshell-complete-hostname)

(defun pcomplete/telnet ()
  (require 'pcmpl-unix)
  (pcomplete-opt "xl(pcmpl-unix-user-names)")
  (eshell-complete-hostname))

(defun pcomplete/rsh ()
  "Complete `rsh', which, after the user and hostname, is like xargs."
  (require 'pcmpl-unix)
  (pcomplete-opt "l(pcmpl-unix-user-names)")
  (eshell-complete-hostname)
  (pcomplete-here (funcall pcomplete-command-completion-function))
  (funcall (or (pcomplete-find-completion-function (pcomplete-arg 1))
               pcomplete-default-completion-function)))

(defvar block-size)
(defvar by-bytes)
(defvar dereference-links)
(defvar grand-total)
(defvar human-readable)
(defvar max-depth)
(defvar only-one-filesystem)
(defvar show-all)

(defsubst eshell-du-size-string (size)
  (let* ((str (eshell-printable-size size human-readable block-size t))
         (len (length str)))
    (concat str (if (< len 8)
                    (make-string (- 8 len) ? )))))

(defun eshell-du-sum-directory (path depth)
  "Summarize PATH, and its member directories."
  (let ((entries (eshell-directory-files-and-attributes path))
        (size 0.0))
    (while entries
      (unless (string-match "\\`\\.\\.?\\'" (caar entries))
        (let* ((entry (concat path "/"
                              (caar entries)))
               (symlink (and (stringp (cadr (car entries)))
                             (cadr (car entries)))))
          (unless (or (and symlink (not dereference-links))
                      (and only-one-filesystem
                           (/= only-one-filesystem
                               (nth 12 (car entries)))))
            (if symlink
                (setq entry symlink))
            (setq size
                  (+ size
                     (if (eq t (cadr (car entries)))
                         (eshell-du-sum-directory entry (1+ depth))
                       (let ((file-size (nth 8 (car entries))))
                         (prog1
                             file-size
                           (if show-all
                               (eshell-print
                                (concat (eshell-du-size-string file-size)
                                        entry "\n")))))))))))
      (setq entries (cdr entries)))
    (if (or (not max-depth)
            (= depth max-depth)
            (= depth 0))
        (eshell-print (concat (eshell-du-size-string size)
                              (directory-file-name path) "\n")))
    size))

(defun eshell/du (&rest args)
  "Implementation of \"du\" in Lisp, passing ARGS."
  (setq args (if args
                 (eshell-stringify-list (eshell-flatten-list args))
               '(".")))
  (let ((ext-du (eshell-search-path "du")))
    (if (and ext-du
             (not (catch 'have-ange-path
                    (dolist (arg args)
                      (if (string-equal
                           (file-remote-p (expand-file-name arg) 'method) "ftp")
                          (throw 'have-ange-path t))))))
        (throw 'eshell-replace-command
               (eshell-parse-command (eshell-quote-argument ext-du) args))
      (eshell-eval-using-options
       "du" args
       '((?a "all" nil show-all
             "write counts for all files, not just directories")
         (nil "block-size" t block-size
              "use SIZE-byte blocks (i.e., --block-size SIZE)")
         (?b "bytes" nil by-bytes
             "print size in bytes")
         (?c "total" nil grand-total
             "produce a grand total")
         (?d "max-depth" t max-depth
             "display data only this many levels of data")
         (?h "human-readable" 1024 human-readable
             "print sizes in human readable format")
         (?H "is" 1000 human-readable
             "likewise, but use powers of 1000 not 1024")
         (?k "kilobytes" 1024 block-size
             "like --block-size 1024")
         (?L "dereference" nil dereference-links
             "dereference all symbolic links")
         (?m "megabytes" 1048576 block-size
             "like --block-size 1048576")
         (?s "summarize" 0 max-depth
             "display only a total for each argument")
         (?x "one-file-system" nil only-one-filesystem
             "skip directories on different filesystems")
         (nil "help" nil nil
              "show this usage screen")
         :external "du"
         :usage "[OPTION]... FILE...
Summarize disk usage of each FILE, recursively for directories.")
       (unless by-bytes
         (setq block-size (or block-size 1024)))
       (if (and max-depth (stringp max-depth))
           (setq max-depth (string-to-number max-depth)))
       ;; filesystem support means nothing under Windows
       (if (eshell-under-windows-p)
           (setq only-one-filesystem nil))
       (let ((size 0.0) ange-cache)
         (while args
           (if only-one-filesystem
               (setq only-one-filesystem
                     (nth 11 (eshell-file-attributes
                              (file-name-as-directory (car args))))))
           (setq size (+ size (eshell-du-sum-directory
                               (directory-file-name (car args)) 0)))
           (setq args (cdr args)))
         (if grand-total
             (eshell-print (concat (eshell-du-size-string size)
                                   "total\n"))))))))

(defvar eshell-time-start nil)

(defun eshell-show-elapsed-time ()
  (let ((elapsed (format "%.3f secs\n" (- (float-time) eshell-time-start))))
    (set-text-properties 0 (length elapsed) '(face bold) elapsed)
    (eshell-interactive-print elapsed))
  (remove-hook 'eshell-post-command-hook 'eshell-show-elapsed-time t))

(defun eshell/time (&rest args)
  "Implementation of \"time\" in Lisp."
  (let ((time-args (copy-alist args))
        (continue t)
        last-arg)
    (while (and continue args)
      (if (not (string-match "^-" (car args)))
          (progn
            (if last-arg
                (setcdr last-arg nil)
              (setq args '("")))
            (setq continue nil))
        (setq last-arg args
              args (cdr args))))
    (eshell-eval-using-options
     "time" args
     '((?h "help" nil nil "show this usage screen")
       :external "time"
       :show-usage
       :usage "COMMAND...
Show wall-clock time elapsed during execution of COMMAND.")
     (setq eshell-time-start (float-time))
     (add-hook 'eshell-post-command-hook 'eshell-show-elapsed-time nil t)
     ;; after setting
     (throw 'eshell-replace-command
            (eshell-parse-command (car time-args)
;;; http://lists.gnu.org/archive/html/bug-gnu-emacs/2007-08/msg00205.html
                                  (eshell-stringify-list
                                   (eshell-flatten-list (cdr time-args))))))))

(defun eshell/whoami (&rest args)
  "Make \"whoami\" Tramp aware."
  (or (file-remote-p default-directory 'user) (user-login-name)))

(defvar eshell-diff-window-config nil)

(defun eshell-diff-quit ()
  "Restore the window configuration previous to diff'ing."
  (interactive)
  (if eshell-diff-window-config
      (set-window-configuration eshell-diff-window-config)))

(defun nil-blank-string (string)
  "Return STRING, or nil if STRING contains only non-blank characters."
  (cond
    ((string-match "[^[:blank:]]" string) string)
    (nil)))

(autoload 'diff-no-select "diff")

(defun eshell/diff (&rest args)
  "Alias \"diff\" to call Emacs `diff' function."
  (let ((orig-args (eshell-stringify-list (eshell-flatten-list args))))
    (if (or eshell-plain-diff-behavior
            (not (and (eshell-interactive-output-p)
                      (not eshell-in-pipeline-p)
                      (not eshell-in-subcommand-p))))
        (throw 'eshell-replace-command
               (eshell-parse-command "*diff" orig-args))
      (setq args (copy-sequence orig-args))
      (if (< (length args) 2)
          (throw 'eshell-replace-command
                 (eshell-parse-command "*diff" orig-args)))
      (let ((old (car (last args 2)))
            (new (car (last args)))
            (config (current-window-configuration)))
        (if (= (length args) 2)
            (setq args nil)
          (setcdr (last args 3) nil))
        (with-current-buffer
            (condition-case nil
                (diff-no-select
                 old new
                 (nil-blank-string (eshell-flatten-and-stringify args)))
              (error
               (throw 'eshell-replace-command
                      (eshell-parse-command "*diff" orig-args))))
          (when (fboundp 'diff-mode)
            (make-local-variable 'compilation-finish-functions)
            (add-hook
             'compilation-finish-functions
             `(lambda (buff msg)
                (with-current-buffer buff
                  (diff-mode)
                  (set (make-local-variable 'eshell-diff-window-config)
                       ,config)
                  (local-set-key [?q] 'eshell-diff-quit)
                  (if (fboundp 'turn-on-font-lock-if-enabled)
                      (turn-on-font-lock-if-enabled))
                  (goto-char (point-min))))))
          (pop-to-buffer (current-buffer))))))
  nil)

(put 'eshell/diff 'eshell-no-numeric-conversions t)

(defvar locate-history-list)

(defun eshell/locate (&rest args)
  "Alias \"locate\" to call Emacs `locate' function."
  (if (or eshell-plain-locate-behavior
          (not (and (eshell-interactive-output-p)
                    (not eshell-in-pipeline-p)
                    (not eshell-in-subcommand-p)))
          (and (stringp (car args))
               (string-match "^-" (car args))))
      (throw 'eshell-replace-command
             (eshell-parse-command "*locate" (eshell-stringify-list
                                              (eshell-flatten-list args))))
    (save-selected-window
      (let ((locate-history-list (list (car args))))
        (locate-with-filter (car args) (cadr args))))))

(put 'eshell/locate 'eshell-no-numeric-conversions t)

(defun eshell/occur (&rest args)
  "Alias \"occur\" to call Emacs `occur' function."
  (let ((inhibit-read-only t))
    (if (> (length args) 2)
        (error "usage: occur: (REGEXP &optional NLINES)")
      (apply 'occur args))))

(put 'eshell/occur 'eshell-no-numeric-conversions t)

(provide 'em-unix)

(require 'esh-util)
(eval-when-compile
  (require 'eshell)
  (require 'pcomplete))
(require 'compile)

;;;###autoload
(progn
(defgroup eshell-xtra nil
  "This module defines some extra alias functions which are entirely
optional.  They can be viewed as samples for how to write Eshell alias
functions, or as aliases which make some of Emacs's behavior more
naturally accessible within Emacs."
  :tag "Extra alias functions"
  :group 'eshell-module))

;;; Functions:

(autoload 'eshell-parse-command "esh-cmd")

(defun eshell/expr (&rest args)
  "Implementation of expr, using the calc package."
  (if (not (fboundp 'calc-eval))
      (throw 'eshell-replace-command
             (eshell-parse-command "*expr" (eshell-flatten-list args)))
    ;; to fool the byte-compiler...
    (let ((func 'calc-eval))
      (funcall func (eshell-flatten-and-stringify args)))))

(defun eshell/substitute (&rest args)
  "Easy front-end to `intersection', for comparing lists of strings."
  (apply 'substitute (car args) (cadr args) :test 'equal
         (cddr args)))

(defun eshell/count (&rest args)
  "Easy front-end to `intersection', for comparing lists of strings."
  (apply 'count (car args) (cadr args) :test 'equal
         (cddr args)))

(defun eshell/mismatch (&rest args)
  "Easy front-end to `intersection', for comparing lists of strings."
  (apply 'mismatch (car args) (cadr args) :test 'equal
         (cddr args)))

(defun eshell/union (&rest args)
  "Easy front-end to `intersection', for comparing lists of strings."
  (apply 'union (car args) (cadr args) :test 'equal
         (cddr args)))

(defun eshell/intersection (&rest args)
  "Easy front-end to `intersection', for comparing lists of strings."
  (apply 'intersection (car args) (cadr args) :test 'equal
         (cddr args)))

(defun eshell/set-difference (&rest args)
  "Easy front-end to `intersection', for comparing lists of strings."
  (apply 'set-difference (car args) (cadr args) :test 'equal
         (cddr args)))

(defun eshell/set-exclusive-or (&rest args)
  "Easy front-end to `intersection', for comparing lists of strings."
  (apply 'set-exclusive-or (car args) (cadr args) :test 'equal
         (cddr args)))

(defalias 'eshell/ff 'find-name-dired)
(defalias 'eshell/gf 'find-grep-dired)

(defun pcomplete/bcc32 ()
  "Completion function for Borland's C++ compiler."
  (let ((cur (pcomplete-arg 0)))
    (cond
     ((string-match "\\`-w\\([^;]+;\\)*\\([^;]*\\)\\'" cur)
      (pcomplete-here
       '("ali" "amb" "amp" "asc" "asm" "aus" "bbf" "bei" "big" "ccc"
         "cln" "cod" "com" "cpt" "csu" "def" "dig" "dpu" "dsz" "dup"
         "eas" "eff" "ext" "hch" "hid" "ias" "ibc" "ifr" "ill" "nil"
         "lin" "lvc" "mcs" "mes" "mpc" "mpd" "msg" "nak" "ncf" "nci"
         "ncl" "nfd" "ngu" "nin" "nma" "nmu" "nod" "nop" "npp" "nsf"
         "nst" "ntd" "nto" "nvf" "obi" "obs" "ofp" "osh" "ovf" "par"
         "pch" "pck" "pia" "pin" "pow" "prc" "pre" "pro" "rch" "ret"
         "rng" "rpt" "rvl" "sig" "spa" "stl" "stu" "stv" "sus" "tai"
         "tes" "thr" "ucp" "use" "voi" "zdi") (match-string 2 cur)))
     ((string-match "\\`-[LIn]\\([^;]+;\\)*\\([^;]*\\)\\'" cur)
      (pcomplete-here (pcomplete-dirs) (match-string 2 cur)))
     ((string-match "\\`-[Ee]\\(.*\\)\\'" cur)
      (pcomplete-here (pcomplete-dirs-or-entries "\\.[Ee][Xx][Ee]\\'")
                      (match-string 1 cur)))
     ((string-match "\\`-o\\(.*\\)\\'" cur)
      (pcomplete-here (pcomplete-dirs-or-entries "\\.[Oo][Bb][Jj]\\'")
                      (match-string 1 cur)))
     (t
      (pcomplete-opt "3456ABCDEHIKLMNOPRSTUVXabcdefgijklnoptuvwxyz"))))
  (while (pcomplete-here
          (pcomplete-dirs-or-entries "\\.[iCc]\\([Pp][Pp]\\)?\\'"))))

(defalias 'pcomplete/bcc 'pcomplete/bcc32)

(provide 'em-xtra)

(require 'esh-util)

(eval-when-compile
  (require 'esh-mode)
  (require 'eshell)
  (require 'tramp))

;;;###autoload
(progn
 (defgroup eshell-tramp nil
   "This module defines commands that use TRAMP in a way that is
  not transparent to the user.  So far, this includes only the
  built-in su and sudo commands, which are not compatible with
  the full, external su and sudo commands, and require the user
  to understand how to use the TRAMP sudo method."
   :tag "TRAMP Eshell features"
   :group 'eshell-module))

(defun eshell-tramp-initialize ()
  "Initialize the TRAMP-using commands code."
  (when (eshell-using-module 'eshell-cmpl)
    (add-hook 'pcomplete-try-first-hook
              'eshell-complete-host-reference nil t))
  (make-local-variable 'eshell-complex-commands)
  (setq eshell-complex-commands
        (append '("su" "sudo")
                eshell-complex-commands)))

(autoload 'eshell-parse-command "esh-cmd")

(defun eshell/su (&rest args)
  "Alias \"su\" to call TRAMP.

Uses the system su through TRAMP's su method."
  (setq args (eshell-stringify-list (eshell-flatten-list args)))
  (let ((orig-args (copy-tree args)))
    (eshell-eval-using-options
     "su" args
     '((?h "help" nil nil "show this usage screen")
       (?l "login" nil login "provide a login environment")
       (?  nil nil login "provide a login environment")
       :usage "[- | -l | --login] [USER]
Become another USER during a login session.")
     (throw 'eshell-replace-command
            (let ((user "root")
                  (host (or (file-remote-p default-directory 'host)
                            "localhost"))
                  (dir (or (file-remote-p default-directory 'localname)
                           (expand-file-name default-directory)))
                  (prefix (file-remote-p default-directory)))
              (dolist (arg args)
                (if (string-equal arg "-") (setq login t) (setq user arg)))
              ;; `eshell-eval-using-options' does not handle "-".
              (if (member "-" orig-args) (setq login t))
              (if login (setq dir "~/"))
              (if (and prefix
                       (or
                        (not (string-equal
                              "su" (file-remote-p default-directory 'method)))
                        (not (string-equal
                              user (file-remote-p default-directory 'user)))))
                  (eshell-parse-command
                   "cd" (list (format "%s|su:%s@%s:%s"
                                      (substring prefix 0 -1) user host dir)))
                (eshell-parse-command
                 "cd" (list (format "/su:%s@%s:%s" user host dir)))))))))

(put 'eshell/su 'eshell-no-numeric-conversions t)

(defun eshell/sudo (&rest args)
  "Alias \"sudo\" to call Tramp.

Uses the system sudo through TRAMP's sudo method."
  (setq args (eshell-stringify-list (eshell-flatten-list args)))
  (let ((orig-args (copy-tree args)))
    (eshell-eval-using-options
     "sudo" args
     '((?h "help" nil nil "show this usage screen")
       (?u "user" t user "execute a command as another USER")
       :show-usage
       :usage "[(-u | --user) USER] COMMAND
Execute a COMMAND as the superuser or another USER.")
     (throw 'eshell-external
            (let ((user (or user "root"))
                  (host (or (file-remote-p default-directory 'host)
                            "localhost"))
                  (dir (or (file-remote-p default-directory 'localname)
                           (expand-file-name default-directory)))
                  (prefix (file-remote-p default-directory)))
              ;; `eshell-eval-using-options' reads options of COMMAND.
              (while (and (stringp (car orig-args))
                          (member (car orig-args) '("-u" "--user")))
                (setq orig-args (cddr orig-args)))
              (let ((default-directory
                      (if (and prefix
                               (or
                                (not
                                 (string-equal
                                  "sudo"
                                  (file-remote-p default-directory 'method)))
                                (not
                                 (string-equal
                                  user
                                  (file-remote-p default-directory 'user)))))
                          (format "%s|sudo:%s@%s:%s"
                                  (substring prefix 0 -1) user host dir)
                        (format "/sudo:%s@%s:%s" user host dir))))
                (eshell-named-command (car orig-args) (cdr orig-args))))))))

(put 'eshell/sudo 'eshell-no-numeric-conversions t)

(provide 'em-tramp)

;; Local Variables:
;; generated-autoload-file: "esh-groups.el"
;; End:
