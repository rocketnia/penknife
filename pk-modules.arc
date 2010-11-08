; pk-modules.arc


; Copyright (c) 2010 Ross Angle
;
;   Permission is hereby granted, free of charge, to any person
;   obtaining a copy of this software and associated documentation
;   files (the "Software"), to deal in the Software without
;   restriction, including without limitation the rights to use, copy,
;   modify, merge, publish, distribute, sublicense, and/or sell copies
;   of the Software, and to permit persons to whom the Software is
;   furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be
;   included in all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;   MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;   HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;   WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Permission to use this software is also granted under the
; Perl Foundation's Artistic License 2.0. You may use either license,
; at your option.


; This is a plugin for Penknife. To use it, load it any time after you
; load penknife.arc and pk-thin-fn.arc.
;
; This is a module system designed to maintain an Arc-style level of
; hackability. If a library is buggy or incomplete, but modifying one
; of its bindings fixes it, Arc has an interoperability problem: Two
; other libraries that use that library might redefine the same things
; in different ways, which might make them unusable with each other.
; This module system aims to fix that problem by instantiating a new
; instance of a library each time it's used.
;
; First, the module is parsed (in a process which will probably happen
; mostly invisibly, the first time the module is constructed). Then
; other code can construct instances of the module, and this will be
; done by creating a new base environment and executing the already
; compiled expressions on that environment.
;
; TODO: Actually make a way to construct modules from within Penknife,
; so that it does what's described above.


; Declaration listing:
;
; (pk-hyperenv-without hyperenv lexid)
;
; (pk-mutate-with-module lexid env str act-on report-error prompt)
; (pk-module lexid env-constructor str act-on report-error prompt)
; (pk-define-module lexid env-constructor str)
; (pk-define-module-from-file lexid env-constructor filename)


(def pk-hyperenv-without (hyperenv lexid)
  (annotate 'pk-hyperenv (copy rep.hyperenv lexid nil)))


(def pk-mutate-with-module (lexid env str act-on report-error prompt)
  (zap newline-normalizer str)
  ; NOTE: If 'pk-staticenv-read-parse-tl raises an error while
  ; reading, rather than while parsing, this could loop infinitely. We
  ; plan to let the environment support command syntax we can't
  ; predict, such as multiple-word commands or commands with
  ; mismatched brackets, so there isn't an obvious way to separate the
  ; reading phase from the parsing phase.
  (withs (rev-commands nil
          result (pktl act-on report-error
                   (fn ()
                     do.prompt.str  ; Wait for more input.
                     (whenlet (expr) (pk-staticenv-read-parse-tl
                                       env lexid str)
                       (let command
                             (eval
                               `[let _ (pk-make-hyperenv
                                         (',thunk.lexid) _)
                                  ,(pk-optimize-subexpr-meta
                                     expr lexid
                                     (pk-make-hyperenv lexid env)
                                     nil nil)])
                         (push command rev-commands)
                         (list do.command.env)))))
          commands rev.rev-commands
          loader [let remaining-commands commands
                   (list _
                     (pktl act-on report-error
                       (thunk:when remaining-commands
                         (list pop.remaining-commands._))))])
    (list loader result)))

(def pk-module (lexid env-constructor str act-on report-error prompt)
  (withs (env call.env-constructor
          (loader result) (pk-mutate-with-module
                            lexid env str act-on report-error prompt))
    (list (thunk:do.loader:do.env-constructor) env result)))

(def pk-define-module (lexid env-constructor str)
  (pk-module lexid env-constructor str [do] err [do]))

(def pk-define-module-from-file (lexid env-constructor filename)
  (w/infile str filename
    (pk-define-module lexid env-constructor str)))
