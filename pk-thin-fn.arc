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
; load penknife.arc and pk-util.arc.
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


; Declaration listing:
;
; pk-nometa*                       ; value of type 'pk-ad-hoc-meta
; (pk-env-shadow-sobj self binds)                ; rulebook
; (pk-copy-hyperenv hyperenv)
; (pk-hyperenv-shadow-assoclist hyperenv binds)
;
; (pk-mangle hyped-sym)
;
; (pk-captures-hyperenv self)  ; rulebook
;
; (odedup self (o test rc.oiso2))  ; rulebook
;
; (def-pk-optimize-expr type . body)                           ; macro
; (def-pk-optimize-expr-meta type . body)                      ; macro
; (pk-optimize-expr self lexid dyn-hyperenv local-lex env-lex)
;   ; rulebook
; (pk-optimize-expr-meta self lexid dyn-hyperenv local-lex env-lex)
;   ; rulebook
;
; < some external rules using 'def-pk-eval >
;
; (pk-finish-fn args rest body meta lexid static-hyperenv)
; (pk-thin-fn-rest-compiler compiled-op body lexid static-hyperenv)
; (pk-thin-fn-compiler compiled-op body lexid static-hyperenv)
;
; Penknife  [tf [args$&] body&]            ; syntax
; Penknife  [tf* [args$&] restarg$ body&]  ; syntax
;
;
; Type listing:
;
; pk-lambdacalc-thin-fn
;   rep: A list which supports the following fields:
;   rep._.0:  A proper list of hyped symbols representing the non-rest
;             parameters of this lambda form.
;   rep._.1:  If non-nil, a singleton proper list containing a hyped
;             symbol representing the rest parameter of this lambda
;             form.
;   rep._.2:  A proper list of the expressions comprising the body of
;             this lambda form, where each expression is a value of
;             one of the 'pk-lambdacalc-[something] types.


(= pk-nometa* (pk-meta))

(rc:ontype pk-env-shadow-sobj (binds) pk-ad-hoc-env pk-ad-hoc-env
  (let rep (apply copy (rep.self)
             (ut:mappendlet (lexid (meta)) tablist.binds
               (list lexid (list pk-make-ad-hoc-binding-meta.meta))))
    (annotate 'pk-ad-hoc-env thunk.rep)))

(def pk-copy-hyperenv (hyperenv)
  (annotate 'pk-hyperenv (copy rep.hyperenv)))

; TODO: If all hyperenvironments are really going to use
; 'pk-ad-hoc-env values to shadow environments that don't yet exist,
; then 'pk-ad-hoc-env needs a more official name. However,
; hyperenvironments should probably be more flexible instead.
(def pk-hyperenv-shadow-assoclist (hyperenv binds)
  (ut:ret new-hyperenv pk-copy-hyperenv.hyperenv
    (let binds-sobjs (table)
      (each (hyped-sym meta) binds
        (let (lexid name) rep.hyped-sym
          (or= rep.new-hyperenv.lexid (let env (pk-make-ad-hoc-env)
                                        (list env env)))
          (= (.name:or= do.binds-sobjs.lexid (table)) list.meta)))
      (each (lexid (local-env global-env)) rep.new-hyperenv
        (= rep.new-hyperenv.lexid
             (list (pk-env-shadow-sobj
                     local-env (or do.binds-sobjs.lexid (table)))
                   global-env))))))


; Pick an unlikely-to-write name without being too obscure and without
; accidentally using ssyntax (even custom ssyntax hacked onto Arc,
; within reason).
(def pk-mangle (hyped-sym)
  (let mangle-sym
         (fn (name)
           (tostring:w/instring s (string:or name "nil")
             ; NOTE: Jarc's readc returns the character equivalent of
             ; -1 on EOF.
             (whilet char (check readc.s [and _ (~is int._ -1)])
               (if (or letter.char digit.char)
                 writec.char
                   (is char #\-)
                 (pr "--")
                 (pr "-u" (coerce int.char 'string 16) "-")))))
    (sym:+ "pk--" (do.mangle-sym rep.hyped-sym.0) "-s-"
           (do.mangle-sym rep.hyped-sym.1))))


(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-call pk-lambdacalc-call
  (some pk-captures-hyperenv rep.self))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-call-set pk-lambdacalc-call-set
  (some pk-captures-hyperenv rep.self))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-call-meta pk-lambdacalc-call-meta
  (some pk-captures-hyperenv rep.self))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-literal pk-lambdacalc-literal
  nil)

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-literal-meta pk-lambdacalc-literal-meta
  nil)

(rc:ontype pk-captures-hyperenv () pk-lambdacalc-var pk-lambdacalc-var
  nil)

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-var-meta pk-lambdacalc-var-meta
  nil)

(rc:ontype pk-captures-hyperenv () pk-lambdacalc-set pk-lambdacalc-set
  (pk-captures-hyperenv rep.self.1))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-set-meta pk-lambdacalc-set-meta
  (pk-captures-hyperenv rep.self.1))

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-demeta pk-lambdacalc-demeta
  nil)

(rc:ontype pk-captures-hyperenv ()
             pk-lambdacalc-thin-fn pk-lambdacalc-thin-fn
  (some pk-captures-hyperenv rep.self.2))


(rc:ontype odedup ((o test rc.oiso2)) rc.list list
  (rev:ut:ret acc nil
    (each elem self
      (unless (some [do.test elem _] acc)
        (push elem acc)))))


(mac def-pk-optimize-expr (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn (fn (self tagged-self lexid dyn-hyperenv
                             local-lex env-lex fail)
                          ,@body)
       (,rc!ontype pk-optimize-expr
                     (lexid dyn-hyperenv local-lex env-lex)
                     ,type ,type
         (,g-backing-fn rep.self self lexid dyn-hyperenv local-lex
                        env-lex fail))
       (,rc!ontype pk-optimize-expr-meta
                     (lexid dyn-hyperenv local-lex env-lex)
                     ,type ,type
         `(pk-meta result
            ,(,g-backing-fn rep.self self lexid dyn-hyperenv local-lex
                            env-lex fail))))))

(mac def-pk-optimize-expr-meta (type . body)
  (w/uniq g-backing-fn
    `(let ,g-backing-fn (fn (self tagged-self lexid dyn-hyperenv
                             local-lex env-lex fail)
                          ,@body)
       (,rc!ontype pk-optimize-expr
                     (lexid dyn-hyperenv local-lex env-lex)
                     ,type ,type
         `(pk-demeta ,(,g-backing-fn rep.self self lexid dyn-hyperenv
                                     local-lex env-lex fail)))
       (,rc!ontype pk-optimize-expr-meta
                     (lexid dyn-hyperenv local-lex env-lex)
                     ,type ,type
         (,g-backing-fn rep.self self lexid dyn-hyperenv local-lex
                        env-lex fail)))))

(def-pk-optimize-expr pk-lambdacalc-call
  `(pk-call
     ,@(map [pk-optimize-expr _ lexid dyn-hyperenv local-lex env-lex]
            self)))

(def-pk-optimize-expr pk-lambdacalc-call-set
  `(pk-call-set
     ,@(map [pk-optimize-expr _ lexid dyn-hyperenv local-lex env-lex]
            self)))

(def-pk-optimize-expr-meta pk-lambdacalc-call-meta
  `(pk-call-meta
     ,@(map [pk-optimize-expr _ lexid dyn-hyperenv local-lex env-lex]
            self)))

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
  (if (oi.opos local-lex self)
    `(pk-demeta ,pk-mangle.self)
      (oi.opos env-lex self)
    `(pk-dyn-hyperenv-get _ (',thunk.self))
    (let binding (pk-dyn-hyperenv-ensure-binding dyn-hyperenv self)
      `(pk-binding-get (',thunk.binding)))))

(def-pk-optimize-expr-meta pk-lambdacalc-var-meta
  (if (oi.opos local-lex self)
    pk-mangle.self
      (oi.opos env-lex self)
    `(pk-dyn-hyperenv-get-meta _ (',thunk.self))
    (let binding (pk-dyn-hyperenv-ensure-binding dyn-hyperenv self)
      `(pk-binding-get-meta (',thunk.binding)))))

(def-pk-optimize-expr pk-lambdacalc-set
  (withs ((var val-expr) self
          val (pk-optimize-expr
                val-expr lexid dyn-hyperenv local-lex env-lex))
    (if (oi.opos local-lex var)
      `(assign ,pk-mangle.var (pk-meta result ,val))
        (oi.opos env-lex var)
      `(pk-dyn-hyperenv-set _ (',thunk.var) ,val)
      (let binding (pk-dyn-hyperenv-ensure-binding dyn-hyperenv var)
        `(pk-binding-set (',thunk.binding) ,val)))))

(def-pk-optimize-expr pk-lambdacalc-set-meta
  (withs ((var val-expr) self
          val (pk-optimize-expr
                val-expr lexid dyn-hyperenv local-lex env-lex))
    (if (oi.opos local-lex var)
      `(assign ,pk-mangle.var ,val)
        (oi.opos env-lex var)
      `(pk-dyn-hyperenv-set-meta _ (',thunk.var) ,val)
      (let binding (pk-dyn-hyperenv-ensure-binding dyn-hyperenv var)
        `(pk-binding-set-meta (',thunk.binding) ,val)))))

(def-pk-optimize-expr pk-lambdacalc-demeta
  (pk-optimize-expr-meta
    car.self lexid dyn-hyperenv local-lex env-lex))

(def-pk-optimize-expr pk-lambdacalc-thin-fn
  (withs ((args rest body)  self
          capturing         (some pk-captures-hyperenv body)
          arg-set           (odedup:join args rest)
          inner-local-lex   (union rc.oiso2
                              local-lex (unless capturing arg-set))
          inner-env-lex     (union rc.oiso2
                              env-lex (when capturing arg-set)))
    `(fn ,(ut.join-end (map pk-mangle args)
                       (when rest (pk-mangle car.rest)))
       ,@(when rest
           (let var (pk-mangle car.rest)
             `((assign ,var (copylist ,var)))))
       ,@(map [let _ pk-mangle._ `(assign ,_ (pk-meta result ,_))]
              arg-set)
       ,@(let body
                (map [pk-optimize-expr _ lexid dyn-hyperenv
                                       inner-local-lex inner-env-lex]
                     body)
           (case capturing nil body
             `((let _ (pk-hyperenv-shadow-assoclist _
                        (list ,@(map [do `(list (',thunk._)
                                                ,pk-mangle._)]
                                     arg-set)))
                 ,@body)))))))


; NOTE: In a compiled expression, when the current dynamic
; hyperenvironment might be captured, it's in the variable _.
(def-pk-eval pk-lambdacalc-thin-fn
  (withs ((args rest body)  self
          capturing         (some pk-captures-hyperenv body)
          arg-set           (odedup:join args rest)
          local-lex         (unless capturing arg-set)
          env-lex           (when capturing arg-set))
    (eval `(fn ,(ut.join-end (map pk-mangle args)
                             (when rest (pk-mangle car.rest)))
             ,@(when rest
                 (let var (pk-mangle car.rest)
                   `((assign ,var (copylist ,var)))))
             ,@(map [let _ pk-mangle._
                      `(assign ,_ (pk-meta result ,_))]
                    arg-set)
             ,@(let body (map [pk-optimize-expr _ lexid dyn-hyperenv
                                                local-lex env-lex]
                              body)
                 (case capturing nil body
                   `((let _ (pk-hyperenv-shadow-assoclist
                              (',thunk.dyn-hyperenv)
                              (list ,@(map [do `(list (',thunk._)
                                                      ,pk-mangle._)]
                                           arg-set)))
                       ,@body))))))))


(def pk-finish-fn (args rest body meta lexid static-hyperenv)
  (let local-static-hyperenv
         (pk-hyperenv-shadow-assoclist static-hyperenv
           (map [list _ meta] (join args rest)))
    (pk-attach:annotate 'pk-lambdacalc-thin-fn
      (list args rest
        (map [pk-detach:pk-fork-to-get:pk-soup-compile
               _ lexid local-static-hyperenv]
             body)))))

(def pk-thin-fn-rest-compiler (compiled-op body lexid static-hyperenv)
  (let token-args otokens.body
    (unless (<= 3 len.token-args)
      (err:+ "A thin-fn-rest body didn't have at least three words "
             "in it."))
    (withs ((args rest . body) token-args
            check
              [or _ (err "A fn-rest parameter wasn't an identifier.")]
            args (map check (pk-identifier-list args lexid))
            rest (do.check:pk-soup-identifier rest lexid))
      (pk-compile-leaf-from-thunk
        (pk-hyperenv-get static-hyperenv lexid)
        (thunk:pk-finish-fn
          args list.rest body pk-nometa* lexid static-hyperenv)))))

(def pk-thin-fn-compiler (compiled-op body lexid static-hyperenv)
  (let token-args otokens.body
    (unless (<= 2 len.token-args)
      (err "A thin-fn body didn't have at least two words in it."))
    (withs ((args . body) token-args
            check [or _ (err "A fn parameter wasn't an identifier.")]
            args (map check (pk-identifier-list args lexid)))
      (pk-compile-leaf-from-thunk
        (pk-hyperenv-get static-hyperenv lexid)
        (thunk:pk-finish-fn
          args nil body pk-nometa* lexid static-hyperenv)))))


(pk-dynenv-set-meta pk-replenv* 'tf pk-wrap-op.pk-thin-fn-compiler)

(pk-dynenv-set-meta pk-replenv* 'tf*
  pk-wrap-op.pk-thin-fn-rest-compiler)
