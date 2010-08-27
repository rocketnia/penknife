; pk-thin-fn.arc


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


; This is a plugin for Penknife. To use it, load it just after you
; load penknife.arc.
;
; This installs some lambda forms, 'tf and 'tf*, which compile to a
; new Penknife expression type, 'pk-lambdacalc-thin-fn. When an
; expression of this type is evaluated, it's compiled into an Arc
; expression, and that Arc expression is evaluated to produce the
; closure. The point of this process is to make the resulting closure
; faster to call later on, and to give it a smaller memory footprint.
;
; Whether this optimization is generally successful has yet to be
; seen, since no other kinds of Penknife lambda semantics have been
; attempted.


; Definition listing:
;
; (pk-staticenv-shadow-list self vars)  ; rulebook
; (pk-dynenv-shadow-sobj self binds)    ; rulebook
;
; (pk-mangle name)
;
; (pk-captures-env self)  ; rulebook
;
; (def-pk-optimize-expr type . body)                     ; macro
; (def-pk-optimize-expr-meta type . body)                ; macro
; (pk-optimize-expr self dynenv local-lex env-lex)       ; rulebook
; (pk-optimize-expr-meta self dynenv local-lex env-lex)  ; rulebook
;
; (pk-thin-fn-rest-compiler compiled-op body staticenv)
; (pk-thin-fn-compiler compiled-op body staticenv)
;
;
; Type listing:
;
; pk-lambdacalc-thin-fn
;   rep: A list which supports the following fields:
;   rep._.0:  A proper list of symbols representing the non-rest
;             parameters of this lambda form.
;   rep._.1:  If non-nil, a singleton proper list containing a symbol
;             representing the rest parameter of this lambda form.
;   rep._.2:  A proper list of the expressions comprising the body of
;             this lambda form, where each expression is a value of
;             one of the 'pk-lambdacalc-[something] types.


(rc:ontype pk-staticenv-shadow-list (vars) pk-ad-hoc-env pk-ad-hoc-env
  (annotate 'pk-ad-hoc-env
    (apply copy rep.self (mappend [list _ nil] vars))))

(rc:ontype pk-dynenv-shadow-sobj (binds) pk-ad-hoc-env pk-ad-hoc-env
  (annotate 'pk-ad-hoc-env
    (apply copy rep.self
      (mappend [list _.0 (list:pk-make-ad-hoc-binding-meta _.1.0)]
               tablist.binds))))


; Pick an unlikely-to-write name without being too obscure and without
; accidentally using ssyntax (even custom ssyntax hacked onto Arc,
; within reason).
(def pk-mangle (name)
  (sym:tostring:w/instring s (string:or name "nil")
    (pr "pk--")
    ; NOTE: Jarc's readc returns the character equivalent of -1 on
    ; EOF.
    (whilet char (check readc.s [and _ (~is int._ -1)])
      (if (or letter.char digit.char)
        writec.char
          (is char #\-)
        (pr "--")
        (pr "-u" (coerce int.char 'string 16) "-")))))


(rc:ontype pk-captures-env () pk-lambdacalc-call pk-lambdacalc-call
  (some pk-captures-env rep.self))

(rc:ontype pk-captures-env ()
             pk-lambdacalc-call-set pk-lambdacalc-call-set
  (some pk-captures-env rep.self))

(rc:ontype pk-captures-env ()
             pk-lambdacalc-call-meta pk-lambdacalc-call-meta
  (some pk-captures-env rep.self))

(rc:ontype pk-captures-env ()
             pk-lambdacalc-literal pk-lambdacalc-literal
  nil)

(rc:ontype pk-captures-env ()
             pk-lambdacalc-literal-meta pk-lambdacalc-literal-meta
  nil)

(rc:ontype pk-captures-env () pk-lambdacalc-var pk-lambdacalc-var
  nil)

(rc:ontype pk-captures-env ()
             pk-lambdacalc-var-meta pk-lambdacalc-var-meta
  nil)

(rc:ontype pk-captures-env () pk-lambdacalc-set pk-lambdacalc-set
  nil)

(rc:ontype pk-captures-env ()
             pk-lambdacalc-set-meta pk-lambdacalc-set-meta
  nil)

(rc:ontype pk-captures-env ()
             pk-lambdacalc-demeta pk-lambdacalc-demeta
  nil)

(rc:ontype pk-captures-env ()
             pk-lambdacalc-thin-fn pk-lambdacalc-thin-fn
  (some pk-captures-env rep.self.2))


(mac def-pk-optimize-expr (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn
            (fn (self tagged-self dynenv local-lex env-lex fail)
              ,@body)
       (,rc!ontype pk-optimize-expr (dynenv local-lex env-lex)
                     ,type ,type
         (,g-backing-fn rep.self self dynenv local-lex env-lex fail))
       (,rc!ontype pk-optimize-expr-meta (dynenv local-lex env-lex)
                     ,type ,type
         `(pk-meta result
            ,(,g-backing-fn
               rep.self self dynenv local-lex env-lex fail))))))

(mac def-pk-optimize-expr-meta (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn
            (fn (self tagged-self dynenv local-lex env-lex fail)
              ,@body)
       (,rc!ontype pk-optimize-expr (dynenv local-lex env-lex)
                     ,type ,type
         `(pk-demeta ,(,g-backing-fn
                        rep.self self dynenv local-lex env-lex fail)))
       (,rc!ontype pk-optimize-expr-meta (dynenv local-lex env-lex)
                     ,type ,type
         (,g-backing-fn
           rep.self self dynenv local-lex env-lex fail)))))

(def-pk-optimize-expr pk-lambdacalc-call
  `(pk-call
     ,@(map [pk-optimize-expr _ dynenv local-lex env-lex] self)))

(def-pk-optimize-expr pk-lambdacalc-call-set
  `(pk-call-set
     ,@(map [pk-optimize-expr _ dynenv local-lex env-lex] self)))

(def-pk-optimize-expr-meta pk-lambdacalc-call-meta
  `(pk-call-meta
     ,@(map [pk-optimize-expr _ dynenv local-lex env-lex] self)))

(def-pk-optimize-expr pk-lambdacalc-literal
  (zap car self)
  `(',thunk.self))

(def-pk-optimize-expr-meta pk-lambdacalc-literal-meta
  (zap car self)
  `(',thunk.self))

; NOTE: In the following rules, we wrap the bindings we get in thunks
; so that their identities are preserved in official Arc 3.1 and
; Anarki. If we just included the binding directly in the quote, using
; "',binding", then (assuming the binding is an Arc tagged value,
; which is a Racket vector) Racket would evaluate the quoted vector by
; copying it.

(def-pk-optimize-expr pk-lambdacalc-var
  (if (mem self local-lex)
    `(pk-demeta ,pk-mangle.self)
      (mem self env-lex)
    `(pk-dynenv-get _ ',self)
    (let binding (pk-dynenv-ensure-binding dynenv self)
      `(pk-binding-get (',thunk.binding)))))

(def-pk-optimize-expr-meta pk-lambdacalc-var-meta
  (if (mem self local-lex)
    pk-mangle.self
      (mem self env-lex)
    `(pk-dynenv-get-meta _ ',self)
    (let binding (pk-dynenv-ensure-binding dynenv self)
      `(pk-binding-get-meta (',thunk.binding)))))

(def-pk-optimize-expr pk-lambdacalc-set
  (withs ((var val-expr) self
          val (pk-optimize-expr val-expr dynenv local-lex env-lex))
    (if (mem var local-lex)
      `(assign ,pk-mangle.var (pk-meta result ,val))
        (mem var env-lex)
      `(pk-dynenv-set _ ',var ,val)
      (let binding (pk-dynenv-ensure-binding dynenv var)
        `(pk-binding-set (',thunk.binding) ,val)))))

(def-pk-optimize-expr pk-lambdacalc-set-meta
  (withs ((var val-expr) self
          val (pk-optimize-expr val-expr dynenv local-lex env-lex))
    (if (mem var local-lex)
      `(assign ,pk-mangle.var ,val)
        (mem var env-lex)
      `(pk-dynenv-set-meta _ ',var ,val)
      (let binding (pk-dynenv-ensure-binding dynenv var)
        `(pk-binding-set-meta (',thunk.binding) ,val)))))

(def-pk-optimize-expr pk-lambdacalc-demeta
  (pk-optimize-expr-meta car.self dynenv local-lex env-lex))

(def-pk-optimize-expr pk-lambdacalc-thin-fn
  (withs ((args rest body)  self
          capturing-env     (some pk-captures-env body)
          arg-set           (dedup:join args rest)
          inner-local-lex   (union is local-lex
                                      (unless capturing-env arg-set))
          inner-env-lex     (union is env-lex
                                      (when capturing-env arg-set)))
    `(fn ,(ut.join-end (map pk-mangle args)
                       (when rest (pk-mangle car.rest)))
       ,@(when rest
           (let var (pk-mangle car.rest)
             `((assign ,var (copylist ,var)))))
       ,@(map [let _ pk-mangle._ `(assign ,_ (pk-meta result ,_))]
              arg-set)
       ,@(let body (map [pk-optimize-expr
                          _ dynenv inner-local-lex inner-env-lex]
                        body)
           (case capturing-env nil body
             `((let _ (pk-dynenv-shadow-sobj _
                        (w/table it
                          ,@(map [do
                                   `(sref it (list ,pk-mangle._) ',_)]
                                 arg-set)))
                 ,@body)))))))


; NOTE: In a compiled expression, when the current dynamic environment
; might be captured, it's in the variable _.
(def-pk-eval pk-lambdacalc-thin-fn
  (withs ((args rest body)  self
          capturing-env     (some pk-captures-env body)
          arg-set           (dedup:join args rest)
          local-lex         (unless capturing-env arg-set)
          env-lex           (when capturing-env arg-set))
    (eval `(fn ,(ut.join-end (map pk-mangle args)
                             (when rest (pk-mangle car.rest)))
             ,@(when rest
                 (let var (pk-mangle car.rest)
                   `((assign ,var (copylist ,var)))))
             ,@(map [let _ pk-mangle._
                      `(assign ,_ (pk-meta result ,_))]
                    arg-set)
             ,@(let body (map [pk-optimize-expr
                                _ dynenv local-lex env-lex]
                              body)
                 (case capturing-env nil body
                   `((let _ (pk-dynenv-shadow-sobj ',dynenv
                              (w/table it
                                ,@(map [do `(sref it
                                                  (list ,pk-mangle._)
                                                  ',_)]
                                       arg-set)))
                       ,@body))))))))


(def pk-thin-fn-rest-compiler (compiled-op body staticenv)
  (let token-args otokens.body
    (unless (<= 3 len.token-args)
      (err:+ "A thin-fn-rest body didn't have at least three words "
             "in it."))
    (let (args rest . body) token-args
      (unless (and (single rep.args)
                   (single rep.args.0)
                   (isa rep.args.0.0 'pk-bracketed-soup))
        (err:+ "A thin-fn-rest parameter list wasn't a "
               "'pk-bracketed-soup."))
      (zap otokens:car:rep:caar:rep args)
      (unless (all pk-soup-identifier (cons rest args))
        (err "A thin-fn-rest parameter wasn't an identifier."))
      (pk-compile-leaf-from-thunk staticenv
        (thunk:let innerenv (pk-staticenv-shadow-list staticenv
                              (cons (zap sym:car:rep rest)
                                    (zap [map sym:car:rep _] args)))
          (annotate 'pk-lambdacalc-thin-fn
            (list args list.rest
              (map [pk-fork-to-get:pk-soup-compile _ innerenv]
                   body))))))))

(def pk-thin-fn-compiler (compiled-op body staticenv)
  (let token-args otokens.body
    (unless (<= 2 len.token-args)
      (err "A thin-fn body didn't have at least two words in it."))
    (let (args . body)  token-args
      (unless (and (single rep.args)
                   (single rep.args.0)
                   (isa rep.args.0.0 'pk-bracketed-soup))
        (err "A thin-fn parameter list wasn't a 'pk-bracketed-soup."))
      (zap otokens:car:rep:caar:rep args)
      (unless (all pk-soup-identifier args)
        (err "A thin-fn parameter wasn't an identifier."))
      (zap [map sym:car:rep _] args)
      (pk-compile-leaf-from-thunk staticenv
        (thunk:let innerenv (pk-staticenv-shadow-list staticenv args)
          (annotate 'pk-lambdacalc-thin-fn
            (list args nil
              (map [pk-fork-to-get:pk-soup-compile _ innerenv]
                   body))))))))


(pk-dynenv-set-meta pk-replenv* 'tf
  (pk-meta compile-fork (list:pk-compile-fork-from-op
                          pk-thin-fn-compiler)))

(pk-dynenv-set-meta pk-replenv* 'tf*
  (pk-meta compile-fork (list:pk-compile-fork-from-op
                          pk-thin-fn-rest-compiler)))
