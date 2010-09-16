; pk-qq.arc


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
; load penknife.arc and pk-thin-fn.arc. To use 'hm and 'hm*, you
; should also load pk-hefty-fn.arc at some point, but it doesn't
; matter whether you load that file before or after this one.
;
; This installs some utilities for writing macros. Macros are deeply
; tied together with quasiquotation and soup in Penknife, and it's
; probably not easy to explain part of it without explaining the whole
; thing.
;
; TODO: Explain it. Yes, the whole thing.
;
; TODO: Give the following comment some more context.
;
; Instead of generating a brand new lexid and capturing a brand new
; closure of the dynamic hyperenvironment at each quasiquote usage, we
; generate a new quasiquote form each time a macro is called, so that
; so that the same variables can be used in multiple pieces of
; generated code that are stitched together. This quasiquotation
; operator uses a brand new lexid, but the global static environment
; it associates with that lexid is always the environment which was
; the local dynamic environment at the time the macro was defined.
;
; Each parameter of the macro (which is necessarily a
; 'pk-attached-soup value) is also given a syntactic meaning as a
; quasiquotation operator which invades that parameter's lexid and
; uses the parameter's global static hyperenvironment.
;
; For uniformity's sake, the regular qq operator itself is a magic
; parameter of every macro, and it's backed by a 'pk-attached-soup
; value which contains the unique lexid, a singleton global static
; hyperenvironment to contain that lexid's mapping, and an empty
; 'pk-soup value.

; This will build a 'pk-lambdacalc-qq expression, and the "basis"
; expression will be obtained by using 'pk-fork-to-get on
; 'compiled-op. Hence, the non-metadata value of a quasiquote operator
; should be the 'pk-attached-soup basis that it invades (and in fact,
; setting it to a new value at runtime, when it's already been used as
; the operator of some compiled quasiquote forms, will change the
; basis those 'pk-lambdacalc-qq expressions use when they evaluate).


; Declaration listing:
;
; (pk-words-hype-staticenv lexid globalenv soup)
; (pk-eval-qq basis dsl handle-splice)
; < some external rules using 'def-pk-eval >
; (pk-captures-hyperenv self)                          ; external rule
; < some external rules using 'def-pk-optimize-expr >
; (pk-qq-compiler compiled-op body lexid static-hyperenv)
;
; (pk-wrapmc dynenv arity varargs func)
; < some external rules using 'def-pk-eval >
; (pk-captures-hyperenv self)                 ; external rule
; < some external rules using 'def-pk-optimize-expr >
; pk-qqmeta*                           ; value of type 'pk-ad-hoc-meta
; (pk-mc-rest-compiler-for build-fn)
; (pk-mc-compiler-for build-fn)
;
; Penknife  [tm qq$ [args$&] body&]
; Penknife  [tm* qq$ [args$&] rest$ body&]
; Penknife  [hm qq$ [args$&] body&]
; Penknife  [hm* qq$ [args$&] rest$ body&]
; Penknife  [wrap-op op]
;
;
; Type listing:
;
; pk-attached-soup
;   rep: A list which supports the following fields:
;   rep._.0:  A symbol to be used as a lexid (lexical ID).
;   rep._.1:  A hyperenvironment containing global static environments
;             to use when compiling this soup.
;   rep._.2:  A 'pk-soup value.
;
; pk-lambdacalc-qq
;   rep: A list which supports the following fields:
;   rep._.0:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will return a 'pk-attached-soup value to
;             use as the basis of this quasiquote form. The basis will
;             provide the lexid and the hyperenvironment to include in
;             the new 'pk-attached-soup value resulting from this
;             quasiquote form.
;   rep._.1:  A list in a special quasiquote DSL. Each element is of
;             one of the following formats:
;
;               (soup _)       - Splice in the soup _.
;               (bracket . _)  - Use the quasiquote DSL _ to build a
;                                'pk-soup value. Wrap that up in a
;                                'pk-bracketed-soup value, and splice
;                                it in as a sip.
;               (splice _)
;                 - Splice in the 'pk-attached-soup value resulting
;                   from the 'pk-lambdacalc-[something] expression _.
;                   This will involve converting each word of its soup
;                   into a word containing only a
;                   'pk-sip-hype-staticenv and keeping track of the
;                   attached hyperenvironment.
;
;             The soup resulting from this DSL will be wrapped up in
;             a new 'pk-attached-soup based on the basis, but adding
;             to that hyperenvironment any lexids mapped by spliced-in
;             'pk-attached-soup values' hyperenvironments. Any
;             conflict between lexid mappings is a runtime error.
;
; pk-lambdacalc-mc
;   rep: A list which supports the following fields:
;   rep._.0:  The number of non-rest arguments to the macro op
;             compiler. This is the minimum number of words that can
;             appear in the body of any form using the macro op.
;   rep._.1:  A boolean indicating, if true, that this is a varargs
;             macro operator, which is to say that any part of the
;             form body that isn't parsed into words for the regular
;             arguments will be given as the final argument of the
;             wrapped function.
;   rep._.2:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will return a function to be wrapped up as
;             a macro op. The first argument to the function will be
;             an empty 'pk-attached-soup value corresponding to the
;             hyperenvironment and lexid captured as this
;             'pk-lambdacalc-mc expression evaluates. Further
;             arguments to the function will be words parsed out of
;             the body of the form the macro op is used in, also
;             wrapped up as 'pk-attached-soup values. If this is a
;             varargs macro op, the final argument of the function
;             will be one more 'pk-attached-soup value corresponding
;             to the soup that remains after those words have been
;             parsed out.


(def pk-words-hype-staticenv (lexid globalenv soup)
  (apply o+ pk-empty-soup*
    (accum acc
      (ut:dstwhilet (margin token rest) o-split-first-token.soup
        do.acc.margin
        (do.acc:pk-soup-singleton:annotate 'pk-sip-hype-staticenv
          (list lexid globalenv token))
        (= soup rest)))))

(def pk-eval-qq (basis dsl handle-splice)
  (case type.basis pk-attached-soup nil
    (err:+ "A value other than a 'pk-attached-soup value was used as "
           "the basis of a quasiquote form."))
  (withs (basis-lexid rep.basis.0
          global-hyperenv (pk-copy-hyperenv rep.basis.1)
          acc-hyperenv [pk-hyperenv-shove global-hyperenv _
                         (+ "Two global static hyperenvironments "
                            "spliced into a quasiquote form "
                            "conflicted.")]
          soup-dsl (afn (dsl)
                     (apply o+ pk-empty-soup*
                       (accum acc
                         (each (op . args) dsl
                           (case op
                             soup     (do.acc car.args)
                             bracket  (do.acc:pk-soup-singleton
                                        (annotate 'pk-bracketed-soup
                                          (list self.args)))
                             splice
                               (let s (do.handle-splice car.args)
                                 (case type.s pk-attached-soup nil
                                   (err:+ "A value other than a "
                                          "'pk-attached-soup value "
                                          "was spliced into a "
                                          "quasiquote form."))
                                 (let (lexid hyperenv soup) rep.s
                                   do.acc-hyperenv.hyperenv
                                   (do.acc:pk-words-hype-staticenv
                                     lexid
                                     (pk-hyperenv-get-global
                                       hyperenv lexid)
                                     soup)))
                               (err:+ "An illegal internal "
                                      "'pk-lambdacalc-qq operator "
                                      "was encountered.")))))))
    (annotate 'pk-attached-soup
      (list basis-lexid global-hyperenv do.soup-dsl.dsl))))

(def-pk-eval pk-lambdacalc-qq
  (pk-eval-qq (pk-eval self.0 lexid dyn-hyperenv) self.1
    [pk-eval _ lexid dyn-hyperenv]))

(rc:ontype pk-captures-hyperenv () pk-lambdacalc-qq pk-lambdacalc-qq
  t)

(def-pk-optimize-expr pk-lambdacalc-qq
  (let optimize-dsl
         (afn (dsl)
           (map [case car._
                  soup     `(,'unquote (',thunk._))
                  bracket  `(bracket ,@(self cdr._))
                  splice
                    `(splice
                       (,'unquote
                         (fn ()
                           ,(pk-optimize-expr _.1
                              lexid dyn-hyperenv local-lex env-lex))))
                    (err:+ "An illegal internal 'pk-lambdacalc-qq "
                           "operator was encountered.")]
                dsl))
    `(pk-eval-qq
       ,(pk-optimize-expr self.0 lexid dyn-hyperenv local-lex env-lex)
       (,'quasiquote ,(optimize-dsl self.1))
       call)))

(def pk-qq-compiler (compiled-op body lexid static-hyperenv)
  (let parse-into-dsl
         (afn (soup)
           (accum acc
             (while:let (margin rest)
                          (o-ltrim soup
                            [~or (is _ #\\)
                                 (isa _ 'pk-bracketed-soup)])
               (unless oi.oempty.margin
                 (do.acc `(soup ,margin)))
               (whenlet (trigger rest) (osplit rest 1)
                 (zap [oref _ 0] trigger)
                 (case trigger #\\
                   (iflet (esccode-soup rest) (osplit rest 1)
                     (caselet esccode (oref esccode-soup 0)
                       #\\  (do (do.acc `(soup ,esccode-soup))
                                (= soup rest))
                       #\,  (let (word rest)
                                   (o-ltrim rest ~soup-whitec)
                              (do.acc
                                `(splice
                                   ,(pk-detach:pk-fork-to-get
                                      (pk-soup-compile
                                        word lexid static-hyperenv))))
                              (= soup rest))
                         (case type.esccode pk-bracketed-soup
                           (let words (otokens rep.esccode.0)
                             (unless single.words
                               (err:+ "A quasiquote bracket escape "
                                      "form didn't have exactly one "
                                      "word in it."))
                             (do.acc `(splice
                                        ,(pk-detach:pk-fork-to-get
                                           (pk-soup-compile
                                             car.words
                                             lexid
                                             static-hyperenv))))
                             (= soup rest))
                           (err:+ "An unrecognized quasiquote escape "
                                  "code was encountered.")))
                     (err:+ "An unescaped backslash was at the end "
                            "of some quasiquoted soup."))
                   (do (do.acc `(bracket ,@(self rep.trigger.0)))
                       (= soup rest)))))))
    (pk-compile-leaf-from-thunk
      (pk-hyperenv-get static-hyperenv lexid)
      (thunk:pk-attach:annotate 'pk-lambdacalc-qq
        (list (pk-detach pk-fork-to-get.compiled-op)
              do.parse-into-dsl.body)))))


(def pk-wrapmc (dynenv arity varargs func)
  (fn (compiled-op body lexid static-hyperenv)
    (let args (n-of arity
                (iflet (margin word rest) o-split-first-token.body
                  (do (= body rest)
                      word)
                  (err:+ "A macro was used without enough words in "
                         "the form body.")))
      (if varargs
        (zap [join _ list.body] args)
        (when o-split-first-token.body
          (err:+ "A macro was used with too many words in the form "
                 "body.")))
      ; TODO: See if we should unwrap word arguments that are
      ; 'pk-sip-hype-staticenv singletons.
      (zap [map [annotate 'pk-attached-soup
                  (list lexid pk-hyperenv-globals.static-hyperenv _)]
                _]
           args)
      (withs (generated-lexid (uniq)
              hyperenv (pk-make-hyperenv generated-lexid dynenv)
              attached-soup
                (annotate 'pk-attached-soup
                  (list generated-lexid hyperenv pk-empty-soup*))
              func-result (apply pk-call func attached-soup args))
        (case type.func-result pk-attached-soup nil
          (err "The result of a macro wasn't a 'pk-attached-soup."))
        (let (result-lexid result-hyperenv result-soup)
               rep.func-result
          (zap otokens result-soup)
          (unless single.result-soup
            (err:+ "The result of a macro didn't contain exactly one "
                   "word."))
          (pk-attach-op.result-hyperenv:pk-soup-compile
            car.result-soup
            result-lexid
            (pk-hyperenv-overlap
              result-hyperenv static-hyperenv)))))))

(def-pk-eval pk-lambdacalc-mc
  (pk-wrapmc dynenv self.0 self.1
    (pk-eval self.2 lexid dyn-hyperenv)))

(rc:ontype pk-captures-hyperenv () pk-lambdacalc-mc pk-lambdacalc-mc
  t)

(def-pk-optimize-expr pk-lambdacalc-mc
  `(pk-wrapmc (pk-hyperenv-get _ ',lexid) ,self.0 ,self.1
     ,(pk-optimize-expr self.2 lexid dyn-hyperenv local-lex env-lex)))

(= pk-qqmeta* pk-wrap-op.pk-qq-compiler)

(def pk-mc-rest-compiler-for (build-fn)
  (fn (compiled-op body lexid static-hyperenv)
    (let token-args otokens.body
      (unless (<= 4 len.token-args)
        (err "A mc-rest body didn't have at least four words in it."))
      (withs ((qq args rest . body) token-args
              argenvs (pk-make-hyperenv)
              shove [iflet (hyped-varname env) _
                      (do (pk-hyperenv-shove argenvs
                            (pk-make-hyperenv
                              pk-hyped-sym-lexid.hyped-varname env)
                            (+ "Two mc-rest parameters had conflicting "
                               "lexid meanings."))
                          hyped-varname)
                      (err "A mc-rest parameter wasn't an identifier.")]
              global-staticenv
                (pk-hyperenv-get-global static-hyperenv lexid)
              qq (do.shove:pk-soup-identifier-with-env
                   qq lexid global-staticenv)
              args (map shove
                     (pk-identifier-list args lexid global-staticenv))
              rest (do.shove:pk-soup-identifier-with-env
                     rest lexid global-staticenv))
        (pk-compile-leaf-from-thunk
          (pk-hyperenv-get static-hyperenv lexid)
          (thunk:let local-static-hyperenv
                       (pk-hyperenv-shadow-assoclist static-hyperenv
                         (map [list _ pk-qqmeta*]
                           (cons qq (cons rest args))))
            (pk-attach-to argenvs
              (annotate 'pk-lambdacalc-mc
                (list len.args t
                  (pk-detach:do.build-fn:pk-attach:annotate
                    'pk-lambdacalc-thin-fn
                    (list (join list.qq args list.rest) nil
                      (map [pk-detach:pk-fork-to-get:pk-soup-compile
                             _ lexid local-static-hyperenv]
                           body))))))))))))

(def pk-mc-compiler-for (build-fn)
  (fn (compiled-op body lexid static-hyperenv)
    (let token-args otokens.body
      (unless (<= 3 len.token-args)
        (err "A mc body didn't have at least three words in it."))
      (withs ((qq args . body) token-args
              argenvs (pk-make-hyperenv)
              shove [iflet (hyped-varname env) _
                      (do (pk-hyperenv-shove argenvs
                            (pk-make-hyperenv
                              pk-hyped-sym-lexid.hyped-varname env)
                            (+ "Two mc parameters had conflicting "
                               "lexid meanings."))
                          hyped-varname)
                      (err "A mc parameter wasn't an identifier.")]
              global-staticenv
                (pk-hyperenv-get-global static-hyperenv lexid)
              qq (do.shove:pk-soup-identifier-with-env
                   qq lexid global-staticenv)
              args (map shove (pk-identifier-list
                                args lexid global-staticenv)))
        (pk-compile-leaf-from-thunk
          (pk-hyperenv-get static-hyperenv lexid)
          (thunk:let local-static-hyperenv
                       (pk-hyperenv-shadow-assoclist static-hyperenv
                         (map [list _ pk-qqmeta*] (cons qq args)))
            (pk-attach-to argenvs
              (annotate 'pk-lambdacalc-mc
                (list len.args nil
                  (pk-detach:do.build-fn:pk-attach:annotate
                    'pk-lambdacalc-thin-fn
                    (list (cons qq args) nil
                      (map [pk-detach:pk-fork-to-get:pk-soup-compile
                             _ lexid local-static-hyperenv]
                           body))))))))))))


(pk-dynenv-set-meta pk-replenv* 'tm
  (pk-wrap-op:pk-mc-compiler-for idfn))

(pk-dynenv-set-meta pk-replenv* 'tm*
  (pk-wrap-op:pk-mc-rest-compiler-for idfn))

(pk-dynenv-set-meta pk-replenv* 'hm
  (pk-wrap-op:pk-mc-compiler-for
    [pk-attach:annotate 'pk-lambdacalc-hefty-fn pk-detach._]))

(pk-dynenv-set-meta pk-replenv* 'hm*
  (pk-wrap-op:pk-mc-rest-compiler-for
    [pk-attach:annotate 'pk-lambdacalc-hefty-fn pk-detach._]))

(pk-dynenv-set pk-replenv* 'wrap-op pk-wrap-op)
