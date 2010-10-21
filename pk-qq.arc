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
; operator uses brand new lexids whose associated global static
; environments are the local dynamic environments that existed at the
; time the macro was defined, and it picks one of those lexids
; depending on the lexid it's used from (i.e. usually inside the
; macro definition).
;
; The qq operator is therefore a parameter of every macro, and for
; its implementation, it's backed by a 'pk-qq-basis value which
; contains the lexid mapping and a global static hyperenvironment.
; (Modifying the value of this variable can indeed change the behavior
; of the quasiquotation.)
;
; Each macro also takes a second, "leak" quasiquotation operator as a
; parameter, and that one invades the lexid and hyperenvironment
; that exist where the macro is used.


; Declaration listing:
;
; (pk-attach-unattached-soup soup lexid env conflict-error)
; (pk-attach-soup-using soup acc-hyperenv)
; (pk-attach-slurp-using self acc-hyperenv)  ; rulebook
; (pk-attach-sip-using self acc-hyperenv)    ; rulebook
;
; (pk-words-hype-staticenv lexid globalenv soup)
; (pk-splice-into-qq self)                            ; rulebook
; (pk-eval-qq context-lexid basis dsl handle-splice)
; < some external rules using 'def-pk-eval >
; (pk-captures-hyperenv self)                         ; external rule
; < some external rules using 'def-pk-optimize-subexpr >
; (pk-qq-parser op-fork body lexid static-hyperenv)
;
; (pk-hyperenv-lexids hyperenv)
;
; (pk-captures-of self)                                ; external rule
; (pk-wrapmc dyn-hyperenv arity varargs func)
; (pk-wrapmc-op dyn-hyperenv arity varargs func)
; < some external rules using 'def-pk-eval >
; (pk-captures-hyperenv self)                          ; external rule
; < some external rules using 'def-pk-optimize-subexpr >
; pk-qqmeta*                           ; value of type 'pk-ad-hoc-meta
; (pk-mc-rest-parser-for build-fn)
; (pk-mc-parser-for build-fn)
;
; Penknife  [tm qq$ leak$ [args$&] body&]
; Penknife  [tm* qq$ leak$ [args$&] rest$ body&]
; Penknife  [hm qq$ leak$ [args$&] body&]
; Penknife  [hm* qq$ leak$ [args$&] rest$ body&]
; Penknife  [wrap-op op]
;
;
; Type listing:
;
; pk-attached-soup
;   rep: A list which supports the following fields:
;   rep._.0:  A lexid (lexical ID).
;   rep._.1:  A hyperenvironment containing global static environments
;             to use when compiling this soup.
;   rep._.2:  A 'pk-soup value.
;
; pk-qq-basis
;   rep: A list which supports the following fields:
;   rep._.0:  A table mapping lexids (lexical IDs) of the macro usage
;             context to singleton lists containing lexids that should
;             be used instead. (Most quasiquote uses will use the
;             non-leak basis provided by a macro call, and the
;             replacement lexids in that case will correspond to local
;             environments captured at the time the macro was created.
;             The leak operator's mapping will be empty.) If a mapping
;             doesn't exist for a lexid, it means the same thing as a
;             mapping from that lexid to a singleton list containing
;             the same lexid. That is to say, if there's no
;             replacement, no replacement is made.
;   rep._.1:  A hyperenvironment containing global static environments
;             to use when compiling the soup resulting from a
;             quasiquote form that uses this basis.
;
; pk-lambdacalc-qq
;   rep: A list which supports the following fields:
;   rep._.0:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will return a 'pk-qq-basis value to use as
;             the basis of this quasiquote form. The basis will
;             provide the lexid and the hyperenvironment to include in
;             the new 'pk-attached-soup value resulting from this
;             quasiquote form.
;   rep._.1:  A list in a special quasiquote DSL. Each element is of
;             one of the following formats:
;
;               (soup _)       - Splice in the soup _.
;               (bracket . _)  - Use the quasiquote DSL _ to build a
;                                'pk-soup value. Wrap that up in a
;                                'pk-sip-brackets value, and splice it
;                                in as a sip.
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
;   rep._.0:  The number of non-rest arguments to the macro op parser.
;             This is the minimum number of words that can appear in
;             the body of any form using the macro op.
;   rep._.1:  A boolean indicating, if true, that this is a varargs
;             macro operator, which is to say that any part of the
;             form body that isn't parsed into words for the regular
;             arguments will be given as the final argument of the
;             wrapped function.
;   rep._.2:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will return a function to be wrapped up as
;             a macro op. The first argument to the function will be
;             a 'pk-qq-basis value corresponding to the
;             hyperenvironment and lexid captured as this
;             'pk-lambdacalc-mc expression evaluates. The second
;             argument will be another 'pk-qq-basis value
;             corresponding to the place the macro is used. Further
;             arguments to the function will be words parsed out of
;             the body of the form the macro op is used in, wrapped up
;             as 'pk-attached-soup values. If this is a varargs macro
;             op, the final argument of the function will be another
;             'pk-attached-soup value corresponding to the soup that
;             remains after those words have been parsed out.
;
; pk-mc-info
;   rep: A list which supports the following fields:
;   rep._.0:  A 'pk-captures value holding the local environments that
;             were captured from the dynamic hyperenvironment as this
;             macro was created.


; TODO: See if a macro's qq operator should check not only what lexid
; it's used in but also whether it's used from within the context of
; the captured hyperenvironment. Currently, it's almost possible to do
; something like [let foo 1 [mac qqfoo [] [meta= qqfoo qq] qq.foo]],
; then [qqfoo], then [mac baz [] qqfoo.foo] to intentionally give a
; macro access to a nonlocal scope, except that [meta= qqfoo qq]
; doesn't actually copy the syntax information for qq. Well, since the
; 'pk-qq-basis value contains the captured hyperenvironment anyway, is
; there really a point in restricting access to it?

; TODO: Add a compilation phase after parsing in order to support
; things like [let foo 1 [mac bar [] qq.foo]] in modules. Macros will
; still need to be expanded during the parsing phase, but their
; particular closure identities should not be shared across different
; instances of the module. Therefore, a macro will need a dynamic
; value that keeps track of its captured hyperenvironment, and
; there'll need to be an intermediate syntax in the parse tree for
; resolving variables in a command using a macro's hyperenvironment
; before that command has started to evaluate.
;
; TODO: The previous TODO is partially underway, using a bit of a
; different approach: Making lexids contain enough information to
; specify how to get to a hyperenvironment from a base environment.
; The lexids have been restructured, and macros now wear their
; captured environments publically enough for them to support being
; swapped out with doppelgangers in each module instance. To finish
; this off, we need to make sure we can stop carrying environments
; around where they don't belong, like (to not-yet-sure degrees)
; 'pk-sip-hype-staticenv, 'pk-attached-soup, and
; 'pk-attached-lambdacalc. Then we'll need to finish up modules and
; make sure these modifications actually work.


; TODO: Figure out what the point of attached soup is if unattached
; soup contains the same information.

(def pk-attach-unattached-soup (soup lexid env conflict-error)
  (let hyperenv (pk-make-hyperenv lexid env)
    (pk-attach-soup-using soup
      [pk-hyperenv-shove hyperenv _ conflict-error])
    (annotate 'pk-attached-soup (list lexid hyperenv soup))))

(def pk-attach-soup-using (soup acc-hyperenv)
  (each slurp rep.soup
    (pk-attach-slurp-using slurp acc-hyperenv)))

(rc:ontype pk-attach-slurp-using (acc-hyperenv) string string
  nil)

(rc:ontype pk-attach-slurp-using (acc-hyperenv) rc.list list
  (each sip self
    (pk-attach-sip-using sip acc-hyperenv)))

(rc:ontype pk-attach-sip-using (acc-hyperenv)
             pk-sip-brackets pk-sip-brackets
  (pk-attach-soup-using rep.self.0 acc-hyperenv))

(rc:ontype pk-attach-sip-using (acc-hyperenv)
             pk-sip-compose pk-sip-compose
  (each op rep.self.0
    (pk-attach-soup-using op acc-hyperenv))
  (pk-attach-soup-using rep.self.1 acc-hyperenv))

(rc:ontype pk-attach-sip-using (acc-hyperenv)
             pk-sip-hype-staticenv pk-sip-hype-staticenv
  (do.acc-hyperenv:pk-make-hyperenv rep.self.0 rep.self.1)
  (pk-attach-soup-using rep.self.2 acc-hyperenv))

(rc:ontype pk-attach-sip-using (acc-hyperenv)
             pk-sip-whitec pk-sip-whitec
  nil)


(def pk-words-hype-staticenv (lexid globalenv soup)
  (apply o+ pk-empty-soup*
    (accum acc
      (ut:dstwhilet (margin token rest) o-split-first-token.soup
        do.acc.margin
        (do.acc:pk-soup-singleton:annotate 'pk-sip-hype-staticenv
          (list lexid globalenv token))
        (= soup rest))
      do.acc.soup)))

(rc:ontype pk-splice-into-qq () pk-attached-soup pk-attached-soup
  (let (lexid hyperenv soup) rep.self
    (pk-words-hype-staticenv
      lexid (pk-hyperenv-get-global hyperenv lexid) soup)))

(rc:ontype pk-splice-into-qq () pk-soup pk-soup
  self)

(def pk-eval-qq (context-lexid basis dsl handle-splice)
  (case type.basis pk-qq-basis nil
    (err "The basis of a quasiquote form wasn't a 'pk-qq-basis."))
  (let soup-dsl (afn (dsl)
                  (apply o+ pk-empty-soup*
                    (accum acc
                      (each (op . args) dsl
                        (case op
                          soup     (do.acc car.args)
                          bracket  (do.acc:pk-soup-singleton
                                     (annotate 'pk-sip-brackets
                                       (list self.args)))
                          splice
                            (do.acc:pk-splice-into-qq
                              (do.handle-splice car.args))
                            (err:+ "An illegal internal "
                                   "'pk-lambdacalc-qq operator was "
                                   "encountered."))))))
    (let basis-lexid
           (aif rep.basis.0.context-lexid car.it context-lexid)
      (pk-attach-unattached-soup do.soup-dsl.dsl basis-lexid
        (pk-hyperenv-get rep.basis.1 basis-lexid)
        (+ "Two global static hyperenvironments spliced into a "
           "quasiquote form conflicted.")))))

(def-pk-eval pk-lambdacalc-qq
  (pk-eval-qq lexid (pk-eval self.0 lexid dyn-hyperenv) self.1
    [pk-eval _ lexid dyn-hyperenv]))

(rc:ontype pk-captures-hyperenv () pk-lambdacalc-qq pk-lambdacalc-qq
  t)

(def-pk-optimize-subexpr pk-lambdacalc-qq
  (let optimize-dsl
         (afn (dsl)
           (map [case car._
                  soup     `(,'unquote (',thunk._))
                  bracket  `(bracket ,@(self cdr._))
                  splice
                    `(splice
                       (,'unquote
                         (fn ()
                           ,(pk-optimize-subexpr _.1
                              lexid dyn-hyperenv local-lex env-lex))))
                    (err:+ "An illegal internal 'pk-lambdacalc-qq "
                           "operator was encountered.")]
                dsl))
    `(pk-eval-qq
       ',lexid
       ,(pk-optimize-subexpr
          self.0 lexid dyn-hyperenv local-lex env-lex)
       (,'quasiquote ,(optimize-dsl self.1))
       call)))

(def pk-qq-parser (op-fork body lexid static-hyperenv)
  (let parse-into-dsl
         (afn (soup)
           (accum acc
             (while:let (margin rest)
                          (o-ltrim soup
                            [~or (is _ #\\)
                                 (isa _ 'pk-sip-brackets)])
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
                                      (pk-parse
                                        word lexid static-hyperenv))))
                              (= soup rest))
                         (case type.esccode pk-sip-brackets
                           (let words (otokens rep.esccode.0)
                             (unless single.words
                               (err:+ "A quasiquote bracket escape "
                                      "form didn't have exactly one "
                                      "word in it."))
                             (do.acc `(splice
                                        ,(pk-detach:pk-fork-to-get
                                           (pk-parse car.words lexid
                                             static-hyperenv))))
                             (= soup rest))
                           (err:+ "An unrecognized quasiquote escape "
                                  "code was encountered.")))
                     (err:+ "An unescaped backslash was at the end "
                            "of some quasiquoted soup."))
                   (do (do.acc `(bracket ,@(self rep.trigger.0)))
                       (= soup rest)))))))
    (pk-parse-leaf-from-thunk (pk-hyperenv-get static-hyperenv lexid)
      (thunk:pk-attach:annotate 'pk-lambdacalc-qq
        (list (pk-detach pk-fork-to-get.op-fork)
              do.parse-into-dsl.body)))))


(def pk-hyperenv-lexids (hyperenv)
  (keys rep.hyperenv))


(rc:ontype pk-captures-of () pk-mc-info pk-mc-info
  rep.self.0)

(def pk-wrapmc (dyn-hyperenv arity varargs func)
  (pk-meta result
             (annotate 'pk-mc-info
               (list:annotate 'pk-captures
                 (listtab:map [list _ (pk-hyperenv-get-safe-local
                                        dyn-hyperenv _)]
                              pk-hyperenv-lexids.dyn-hyperenv)))
           var-forker  (list:pk-var-forker-from-op:pk-wrapmc-op
                          arity varargs func)))

(def pk-wrapmc-op (arity varargs func)
  (fn (op-fork body lexid static-hyperenv)
    (with (args (n-of arity
                  (iflet (margin word rest) o-split-first-token.body
                    (do (= body rest)
                        word)
                    (err:+ "A macro was used without enough words in "
                           "the form body.")))
           global-static-hyperenv pk-hyperenv-globals.static-hyperenv)
      (if varargs
        (zap [join _ list.body] args)
        (when o-split-first-token.body
          (err:+ "A macro was used with too many words in the form "
                 "body.")))
      ; NOTE: We don't unwrap word arguments that are
      ; 'pk-sip-hype-staticenv singletons. Even if that would be
      ; useful behavior, there should eventually be enough soup
      ; manipulation power within Penknife to implement a replacement
      ; macro-building form there.
      (zap [map [annotate 'pk-attached-soup
                  (list lexid global-static-hyperenv _)]
                _]
           args)
      (withs (; TODO: Make a 'pk-fork-to-name method or something so
              ; that we don't have to scrape expressions like this.
              hyped-name (rep:get.1:rep pk-fork-to-get.op-fork)
              dyn-hyperenv
                (pk-captured-hyperenv:pk-dyn-hyperenv-get
                  static-hyperenv hyped-name)
              generated-lexids
                (map [list _ (list:cons rep.hyped-name _)]
                     pk-hyperenv-lexids.dyn-hyperenv)
              generated-hyperenv
                (pk-hyperenv-overlap dyn-hyperenv
                  (apply pk-make-hyperenv
                    (mappend [list _.1.0
                                   (pk-hyperenv-get dyn-hyperenv _.0)]
                             generated-lexids)))
              func-result
                (apply pk-call func
                  (annotate 'pk-qq-basis                    ; qq
                    (list listtab.generated-lexids
                          generated-hyperenv))
                  (annotate 'pk-qq-basis                    ; leak
                    (list (table) global-static-hyperenv))
                  args))
        (case type.func-result pk-attached-soup nil
          (err "The result of a macro wasn't a 'pk-attached-soup."))
        (let (result-lexid result-hyperenv result-soup)
               rep.func-result
          (zap otokens result-soup)
          (unless single.result-soup
            (err:+ "The result of a macro didn't contain exactly one "
                   "word."))
          (pk-parse car.result-soup result-lexid
            (pk-hyperenv-overlap
              result-hyperenv static-hyperenv)))))))

(def-pk-eval pk-lambdacalc-mc
  (pk-wrapmc
    dyn-hyperenv self.0 self.1 (pk-eval self.2 lexid dyn-hyperenv)))

(rc:ontype pk-captures-hyperenv () pk-lambdacalc-mc pk-lambdacalc-mc
  t)

(def-pk-optimize-subexpr pk-lambdacalc-mc
  `(pk-wrapmc _ ,self.0 ,self.1
     ,(pk-optimize-subexpr
        self.2 lexid dyn-hyperenv local-lex env-lex)))

(= pk-qqmeta* pk-wrap-op.pk-qq-parser)

(def pk-mc-rest-parser-for (build-fn)
  (fn (op-fork body lexid static-hyperenv)
    (let token-args otokens.body
      (unless (<= 5 len.token-args)
        (err "A mc-rest body didn't have at least five words in it."))
      (withs ((qq leak args rest . body) token-args
              check
                [or _
                  (err "A mc-rest parameter wasn't an identifier.")]
              qq (do.check:pk-soup-identifier qq lexid)
              leak (do.check:pk-soup-identifier leak lexid)
              args (map check (pk-identifier-list args lexid))
              rest (do.check:pk-soup-identifier rest lexid))
        (pk-parse-leaf-from-thunk
          (pk-hyperenv-get static-hyperenv lexid)
          ; We make sure the expression is attached to the
          ; hyperenvironment it captures.
          (thunk:pk-attach-to pk-hyperenv-globals.static-hyperenv
            (annotate 'pk-lambdacalc-mc
              (list len.args t
                (pk-detach:do.build-fn:pk-finish-fn
                  (join (list qq leak) args list.rest) nil body lexid
                  (pk-hyperenv-shadow-assoclist static-hyperenv
                    (join (map [list _ pk-qqmeta*] (list qq leak))
                          (map [list _ pk-nometa*]
                               (join args list.rest)))))))))))))

(def pk-mc-parser-for (build-fn)
  (fn (op-fork body lexid static-hyperenv)
    (let token-args otokens.body
      (unless (<= 4 len.token-args)
        (err "A mc body didn't have at least four words in it."))
      (withs ((qq leak args . body) token-args
              check
                [or _ (err "A mc parameter wasn't an identifier.")]
              qq (do.check:pk-soup-identifier qq lexid)
              leak (do.check:pk-soup-identifier leak lexid)
              args (map check (pk-identifier-list args lexid)))
        (pk-parse-leaf-from-thunk
          (pk-hyperenv-get static-hyperenv lexid)
          ; We make sure the expression is attached to the
          ; hyperenvironment it captures.
          (thunk:pk-attach-to pk-hyperenv-globals.static-hyperenv
            (annotate 'pk-lambdacalc-mc
              (list len.args nil
                (pk-detach:do.build-fn:pk-finish-fn
                  (join (list qq leak) args) nil body lexid
                  (pk-hyperenv-shadow-assoclist static-hyperenv
                    (join (map [list _ pk-qqmeta*] (list qq leak))
                          (map [list _ pk-nometa*] args))))))))))))


(pk-dynenv-set-meta pk-replenv* 'tm
  (pk-wrap-op:pk-mc-parser-for idfn))

(pk-dynenv-set-meta pk-replenv* 'tm*
  (pk-wrap-op:pk-mc-rest-parser-for idfn))

(pk-dynenv-set-meta pk-replenv* 'hm
  (pk-wrap-op:pk-mc-parser-for
    [pk-attach:annotate 'pk-lambdacalc-hefty-fn pk-detach._]))

(pk-dynenv-set-meta pk-replenv* 'hm*
  (pk-wrap-op:pk-mc-rest-parser-for
    [pk-attach:annotate 'pk-lambdacalc-hefty-fn pk-detach._]))

; TODO: Stop exposing this.
(pk-dynenv-set pk-replenv* 'wrap-op pk-wrap-op)
