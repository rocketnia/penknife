; pk-util.arc


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


; This is a plugin for Penknife. To use it, load it after you load
; penknife.arc.
;
; This installs several utilities in 'pk-replenv*.


; The Penknife declaration listings use the conventions in this
; legend, regardless of whatever meaning they may have in the language
; itself:
;
; [[a b] c]    A unary operator returning a unary operator.
; [a b&]       An operator accepting any number of words.
; a[b~]        An operator which doesn't parse its body into words.
; [a b:]       An operator accepting a setter.
; [a b!]       An operator accepting metadata.
; [a b$]       An operator accepting an identifier.
; [a [b$&]]    An operator accepting a bracketed list of identifiers.
; [idfn.a b]   A syntax operator whose non-syntax form is unary.
; [idfn[a] b]  A syntax operator whose non-syntax form is unary.
; idfn.a       The non-metadata form of an operation.
; [= [a] b]    A nullary operator with setter behavior.
; ; command    The result may have command behavior.
; ; syntax     The result may have syntactic and/or command behavior.
; ; returns z  The result is z.
;
;
; Declaration listing:
;
; (pk-wrap-op op)
;
; (soup->string-force soup)
; (slurp->string-force self)  ; rulebook
; (sip->string-force self)    ; rulebook
; (pk-stringquote-compiler compiled-op body lexid static-hyperenv)
; Penknife  q[string~]
; Penknife  [idfn.q result]
; (pk-drop-to-arc-compiler compiled-op body lexid static-hyperenv)
; Penknife  arc[code~]
; Penknife  arc         ; returns t or nil, indicating support
; (pk-drop-to-plt-compiler compiled-op body lexid static-hyperenv)
; Penknife  plt[code~]
; Penknife  plt         ; returns t or nil, indicating support
; (pk-eval-plt-compiler compiled-op body lexid static-hyperenv)
; Penknife  eval-plt[code~]
; Penknife  eval-plt         ; returns t or nil, indicating support
; pk-jvm-js-engine*          ; nil or a javax.script.ScriptEngine
; (pk-js-compiler compiled-op body lexid static-hyperenv)
; Penknife  js[code~]
; Penknife  js         ; returns t or nil, indicating support
;
; (pk-compose-compiler compiled-op body lexid static-hyperenv)
; (pk-compose . args)
; (pk-sip-compile self lexid static-hyperenv)        ; external rule
; (pk-generic-infix-compiler base-compiler)
; Penknife  [compose ops& op][body~]                 ; syntax
; Penknife  [idfn.[compose funcs& func] args&]
; Penknife  [[compose] result]
; Penknife  [[: ops1&] ops2& op][body~]              ; syntax
; Penknife  [[: ops& op]][body~]                     ; syntax
; Penknife  [idfn.[[: funcs1&] funcs2& func] args&]
; Penknife  [idfn.[[: funcs& func]] args&]
; Penknife  [[[:]] result]
;
; (pk-assign-compiler compiled-op body lexid static-hyperenv)
; Penknife  [= var: val]
;
; (pk-demeta-compiler compiled-op body lexid static-hyperenv)
; Penknife  [meta var!]
; Penknife  [= [meta var$] val]
;
; (pk-infix-call-compiler compiled-op body lexid static-hyperenv)
; Penknife  [. result]        ; syntax
; Penknife  [idfn[.] result]
;
; (pk-infix-inverted-call-compiler
;   compiled-op body lexid static-hyperenv)
; Penknife  ['[body~] op]          ; syntax
; Penknife  [idfn.[' args&] func]
;
; Penknife  [demo]
; Penknife  [+ addends&]
; Penknife  [drop]                  ; command
; Penknife  [drop code]             ; command
; Penknife  idfn.[drop]             ; returns nil
; Penknife  idfn.[drop code]        ; returns nil
; Penknife  help                    ; command
; Penknife  idfn.help               ; returns nil
; Penknife  [[command func] args&]  ; command
; Penknife  [apply func args]
;
;
; Type listing:
;
; pk-sip-compose
;   rep: A list which supports the following fields:
;   rep._.0:  A nonempty proper list of 'pk-soup values representing
;             uncompiled operator expressions to apply in reverse
;             order, in series, to the body. If there is only one
;             operator, it will be applied to the body directly.
;             Otherwise, the first operator will be applied to a
;             new 'pk-sip-compose value containing the rest of the
;             composition information.
;   rep._.1:  A 'pk-soup value representing the uncompiled body to
;             apply the operators to.


; TODO: Put more functionality in here.


(def pk-wrap-op (op)
  (pk-meta compile-fork (list:pk-compile-fork-from-op op)))


(def soup->string-force (soup)
  ; NOTE: On Rainbow, (apply string '("something")) and
  ; (string '("something")) don't have the same result.
  (apply string (map slurp->string-force rep.soup)))

(rc:ontype slurp->string-force () string string
  self)

(rc:ontype slurp->string-force () rc.list list
  ; NOTE: On Rainbow, string:map doesn't work here.
  (apply string (map sip->string-force self)))

(rc:ontype sip->string-force () pk-bracketed-soup pk-bracketed-soup
  (+ "[" (soup->string-force rep.self.0) "]"))

(def pk-stringquote-compiler (compiled-op body lexid static-hyperenv)
  (pk-compile-literal-from-thunk
    (fn () soup->string-force.body)
    (pk-hyperenv-get static-hyperenv lexid)))

(pk-dynenv-set-meta pk-replenv* 'q
  (pk-meta result        idfn
           compile-fork  (list:pk-compile-fork-from-op
                           pk-stringquote-compiler)))

(def pk-drop-to-arc-compiler (compiled-op body lexid static-hyperenv)
  (pk-compile-call-from-thunk
    (thunk:list:pk-attach:pk-noattach:annotate 'pk-lambdacalc-literal
      (list:eval:read:+ "(fn () " soup->string-force.body ")"))
    (pk-staticenv-default-op-compiler:pk-hyperenv-get
      static-hyperenv lexid)))

(pk-dynenv-set-meta pk-replenv* 'arc
  (pk-meta result        t
           compile-fork  (list:pk-compile-fork-from-op
                           pk-drop-to-arc-compiler)))

(def pk-drop-to-plt-compiler (compiled-op body lexid static-hyperenv)
  (pk-compile-call-from-thunk
    (thunk:list:pk-attach:pk-noattach:annotate 'pk-lambdacalc-literal
      (list:if plt
        (plt.eval:plt.read:instring:+
          "(lambda () " soup->string-force.body ")")
        (thunk:err:+ "Dropping to PLT Racket isn't supported on this "
                     "platform.")))
    (pk-staticenv-default-op-compiler:pk-hyperenv-get
      static-hyperenv lexid)))

(pk-dynenv-set-meta pk-replenv* 'plt
  (pk-meta result        (~no plt)    ; NOTE: Jarc dislikes ~~.
           compile-fork  (list:pk-compile-fork-from-op
                           pk-drop-to-plt-compiler)))

(def pk-eval-plt-compiler (compiled-op body lexid static-hyperenv)
  (pk-compile-call-from-thunk
    (thunk:list:pk-attach:pk-noattach:annotate 'pk-lambdacalc-literal
      (list:if plt
        (let exprs (readall soup->string-force.body)
          (thunk:ut:ret result nil
            (each expr exprs
              wipe.result
              (= result plt.eval.expr))))
        (thunk:err:+ "Evaluating PLT Racket isn't supported on this "
                     "platform.")))
    (pk-staticenv-default-op-compiler:pk-hyperenv-get
      static-hyperenv lexid)))

(pk-dynenv-set-meta pk-replenv* 'eval-plt
  (pk-meta result        (~no plt)         ; NOTE: Jarc dislikes ~~.
           compile-fork  (list:pk-compile-fork-from-op
                           pk-eval-plt-compiler)))

(= pk-jvm-js-engine*
  (and jv.jclass!javax-script-ScriptEngineManager
       (jvm!getEngineByName
         (jvm!javax-script-ScriptEngineManager-new)
         "JavaScript")))

; TODO: See what to do about putting semicolons into JavaScript code,
; considering that Penknife treats them as comment characters.
(def pk-js-compiler (compiled-op body lexid static-hyperenv)
  (pk-compile-call-from-thunk
    (thunk:list:pk-attach:pk-noattach:annotate 'pk-lambdacalc-literal
      (list:if pk-jvm-js-engine*
        (thunk:jvm!eval pk-jvm-js-engine* soup->string-force.body)
        (thunk:err:+ "Evaluating JavaScript isn't supported on this "
                     "platform.")))
    (pk-staticenv-default-op-compiler:pk-hyperenv-get
      static-hyperenv lexid)))

(pk-dynenv-set-meta pk-replenv* 'js
  ; NOTE: Jarc dislikes ~~.
  (pk-meta result        (~no pk-jvm-js-engine*)
           compile-fork  (list:pk-compile-fork-from-op
                           pk-js-compiler)))


; We define 'compose such that [[compose a b c] d e] is compiled based
; on the compiler of "a" and a body of this format:
;
;   (annotate 'pk-soup
;     (list:list:annotate 'pk-sip-compose
;       (list (list (annotate 'pk-soup (list "b"))
;                   (annotate 'pk-soup (list "c")))
;             (annotate 'pk-soup (list " d e")))))))
;
(def pk-compose-compiler (compiled-op body lexid static-hyperenv)
  (withs (token-args           otokens.body
          compile-first-arg
            (memo:thunk:if token-args
              (pk-soup-compile car.token-args lexid static-hyperenv)
              (pk-compile-literal-from-thunk
                thunk.idfn (pk-hyperenv-get static-hyperenv lexid))))
    (pk-compile-call-from-thunk
      (thunk:map pk-fork-to-get
        (cons compiled-op
          (when token-args
            (cons call.compile-first-arg
              (map [pk-soup-compile _ lexid static-hyperenv]
                   cdr.token-args)))))
      (fn (compiled-op2 body2 lexid2 static-hyperenv2)
        (let compiled-composed-op call.compile-first-arg
          (pk-fork-to-op compiled-composed-op
                         (case cdr.token-args nil body2
                           (pk-soup-singleton:annotate 'pk-sip-compose
                             (list cdr.token-args body2)))
                         lexid2
                         static-hyperenv2))))))

(def pk-compose args
  (if no.args idfn
    (let (last . rest) rev.args
      (zap rev rest)
      (fn args
        (ut.foldr pk-call (apply pk-call last args) rest)))))

(rc:ontype pk-sip-compile (lexid static-hyperenv)
             pk-sip-compose pk-sip-compose
  (let (ops body) rep.self
    (iflet (first . rest) ops
      (pk-fork-to-op (pk-soup-compile first lexid static-hyperenv)
                     (if rest
                       (pk-soup-singleton:annotate 'pk-sip-compose
                         (list rest body))
                       body)
                     lexid
                     static-hyperenv)
      (do.fail:+ "The syntax was a composition form with nothing "
                 "composed."))))

(def pk-generic-infix-compiler (base-compiler)
  (fn (compiled-op1 body1 lexid1 static-hyperenv1)
    (pk-compile-call-from-thunk
      (thunk:map pk-fork-to-get
        (cons compiled-op1
          (map [pk-soup-compile _ lexid1 static-hyperenv1]
               otokens.body1)))
      (fn (compiled-op2 body2 lexid2 static-hyperenv2)
        (let compile-op
               (memo:thunk:pk-fork-to-op-method:do.base-compiler
                 compiled-op1
                 (let s (pk-soup-singleton:annotate 'pk-soup-whitec
                          nil)
                   (o+ body1 s body2))
                 lexid2
                 static-hyperenv2)
          (pk-compile-call-from-thunk
            (thunk:map pk-fork-to-get
              (cons compiled-op2
                (map [pk-soup-compile _ lexid2 static-hyperenv2]
                     otokens.body2)))
            (fn (compiled-op3 body3 lexid3 static-hyperenv3)
              (pk-call call.compile-op
                compiled-op3 body3 lexid3 static-hyperenv3))))))))

(pk-dynenv-set-meta pk-replenv* 'compose
  (pk-meta result        pk-compose
           compile-fork  (list:pk-compile-fork-from-op
                           pk-compose-compiler)))

(pk-dynenv-set-meta pk-replenv* ':
  (pk-meta result        (fn args1
                           (fn args2
                             (apply pk-compose (join args1 args2))))
           compile-fork  (list:pk-compile-fork-from-op
                           (pk-generic-infix-compiler
                             pk-compose-compiler))))


(def pk-assign-compiler (compiled-op body lexid static-hyperenv)
  (let token-args otokens.body
    (unless (is len.token-args 2)
      (err "An assignment body didn't have exactly two words in it."))
    (pk-compile-leaf-from-thunk
      (pk-hyperenv-get static-hyperenv lexid)
      (thunk:let (var val) token-args
        (pk-fork-to-set
          (pk-soup-compile var lexid static-hyperenv)
          (pk-fork-to-get:pk-soup-compile
            val lexid static-hyperenv))))))

(pk-dynenv-set-meta pk-replenv* '= pk-wrap-op.pk-assign-compiler)


(def pk-demeta-compiler (compiled-op body lexid static-hyperenv)
  (let arg otokens.body
    (unless single.arg
      (err "A meta body didn't have exactly one word in it."))
    (zap car arg)
    (with (getter (memo:thunk:pk-attach:annotate 'pk-lambdacalc-demeta
                    (list:pk-detach:pk-fork-to-meta:pk-soup-compile
                      arg lexid static-hyperenv))
           info (memo:thunk:iflet (hyped-sym env)
                            (pk-soup-identifier-with-env arg lexid
                              (pk-hyperenv-get static-hyperenv lexid))
                  (list hyped-sym (pk-make-hyperenv
                                    pk-hyped-sym-lexid.hyped-sym env))
                  (err "The meta of a non-identifier can't be set.")))
      (annotate 'pk-compile-fork
        (obj get   getter
             set   [let (hyped-varname hyperenv) call.info
                     (pk-attach-to hyperenv
                       (annotate 'pk-lambdacalc-set-meta
                         (list hyped-varname pk-detach._)))]
             meta  getter
             op    (pk-staticenv-default-op-compiler:pk-hyperenv-get
                     static-hyperenv lexid))))))

(pk-dynenv-set-meta pk-replenv* 'meta
  (pk-meta result         idfn
           compile-fork   (list:pk-compile-fork-from-op
                            pk-demeta-compiler)))


(def pk-infix-call-compiler (compiled-op body lexid static-hyperenv)
  (let token-args otokens.body
    (unless single.token-args
      (err "A \".\" body didn't have exactly one word in it."))
    (pk-soup-compile car.token-args lexid static-hyperenv)))

; NOTE: Both Rainbow *and* Jarc consider (string '|.|) to be "|.|".
(pk-dynenv-set-meta pk-replenv* (sym ".")
  (pk-meta result        idfn
           compile-fork  (list:pk-compile-fork-from-op
                           pk-infix-call-compiler)))


(def pk-infix-inverted-call-compiler
       (compiled-op body lexid static-hyperenv)
  (let as-default (memo:thunk:pk-call
                    (pk-staticenv-default-op-compiler:pk-hyperenv-get
                      static-hyperenv lexid)
                    compiled-op body lexid static-hyperenv)
    (annotate 'pk-compile-fork
      (obj get   (memo:thunk:pk-fork-to-get call.as-default)
           set   [err "A once-applied \"'\" form can't be set."]
           meta  (memo:thunk:pk-fork-to-meta call.as-default)
           op    (fn (compiled-op2 body2 lexid2 static-hyperenv2)
                   (let token-args otokens.body2
                     (unless single.token-args
                       (err:+ "The second body of a \"'\" didn't "
                              "have exactly one word in it."))
                     (let compiled-inner-op
                            (pk-soup-compile
                              car.token-args lexid2 static-hyperenv2)
                       (pk-fork-to-op compiled-inner-op
                         body lexid static-hyperenv))))))))

; NOTE: Jarc 17 considers (string '|'|) to be "|'|", and Rainbow
; considers it to be "||" because it parses '|'| as two expressions.
(pk-dynenv-set-meta pk-replenv* (sym "'")
  (pk-meta result        (fn args [apply _ args])
           compile-fork  (list:pk-compile-fork-from-op
                           pk-infix-inverted-call-compiler)))


(pk-dynenv-set pk-replenv* 'demo (thunk:prn "This is a demo."))

(pk-dynenv-set pk-replenv* '+ +)

(pk-dynenv-set pk-replenv* 'drop (annotate 'pk-fn-meta
                                   (list:fn ((o code 'goodbye))
                                     (pk-meta action  (list:fn ())
                                              quit    list.code))))

(pk-dynenv-set-meta pk-replenv* 'help
  (pk-meta action (list:thunk:prn "To exit Penknife, use \"[drop]\", "
                                  "without the quotes.")))

(pk-dynenv-set pk-replenv* 'command [annotate 'pk-fn-meta list._])

(pk-dynenv-set pk-replenv* 'apply (fn args
                                    (apply apply pk-call args)))
