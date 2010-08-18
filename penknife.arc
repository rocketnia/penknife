; penknife.arc


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


; This implements the Penknife programming language, a Blade-like
; scripting language (which may mean nothing to you, since Blade is a
; vaporware hobby project ^_^ ). Penknife, like Blade, is a language
; that emphasizes the use of whatever syntaxes the programmer finds
; best in every situation.
;
; Unlike Blade, which statically compiles a directory structure,
; delaying compilation of certain declarations until the necessary
; syntaxes are known, Penknife interprets an ongoing character stream,
; invoking imperative commands one at a time to build up its
; definition space. This makes it suitable as a REPL language.
;
; Penknife, like Blade, emphasizes a programming style by which
; convenient sub-languages are developed first, and then they're used
; to build data structures that are compiled into whatever performant
; or rigorous forms are necessary. A Penknife program may indeed have
; some behaviors in common with a build script, making system calls to
; invoke machine code compilers, archival utilities, documentation
; generators, and so forth--but without necessarily having any
; non-Penknife code in the project, instead generating that code as
; part of the build process.
;
;
; To use Penknife, you'll need a working Arc setup (either official
; Arc 3.1[1][2][3], Anarki [2][3][4], Jarc [5], or Rainbow [6]), and
; you'll need to have the Lathe library[7]. Note that Penknife is
; *extremely* slow on Jarc 17, and it's not actually a self-sufficient
; language on any of these platforms, since the global Penknife
; environment only has a few test functions and has neither a way to
; define new functions nor a way to run arbitrary Arc code. Right now,
; you're expected to implement those things yourself! It's an
; adventure~! :-p
;
; [1] http://arclanguage.org/item?id=10254
;       "Arc 3.1 (works on latest MzScheme)"
; [2] http://arclanguage.org/item?id=10625
;       "Arc3.1 setuid problem on Windows"
; [3] http://racket-lang.org/ (Racket)
; [4] http://github.com/nex3/arc (Anarki)
; [5] http://jarc.sourceforge.net/
; [6] http://github.com/conanite/rainbow
; [7] http://github.com/rocketnia/lathe


; Definition listing:
;
; ut   ; namespace of Lathe's utils.arc
; mr   ; namespace of Lathe's multival/multirule.arc
; oc   ; namespace of Lathe's multival/order-contribs.arc
; rc   ; namespace of Lathe's orc/orc.arc
; sn   ; namespace of Lathe's imp/sniff.arc
; jv   ; namespace of Lathe's imp/jvm.arc
; plt  ; taken out of Lathe's imp/sniff.arc
; jvm  ; taken out of Lathe's imp/jvm.arc
;
; (fn-input-ify self)  ; rulebook
;
; (newline-normalizer str)
; (comment-ignorer str)
;
; (start-word str (o test ~whitec))
; (finish-bracket-word str (o test whitec))
; (finish-brackets (str))
;
; (orev self)                                ; rulebook
; (o-ltrim self (o test whitec))             ; rulebook
; (o-rtrim self (o test whitec))             ; rulebook
; (o-split-first-token seq (o test whitec))
; (o-split-last-token seq (o test whitec))
; (otokens seq (o test whitec))
;
; (soup->string soup)
; (sip->string self)   ; rulebook
;
; (pk-compile-literal-from-thunk thunk staticenv)
; (pk-function-call-compiler compiled-op body staticenv)
; (pk-stringquote-compiler compiled-op body staticenv)
; (pk-compose-compiler compiled-op body staticenv)
; (pk-assign-compiler compiled-op body staticenv)
; (pk-assignmeta-compiler compiled-op body staticenv)
;
; (pk-meta . args)                      ; macro
; (pk-make-ad-hoc-binding value)
; (pk-make-ad-hoc-binding-meta value)
; (pk-binding-get self)                 ; rulebook
; (pk-binding-get-meta self)            ; rulebook
; (pk-binding-set self new-value)       ; rulebook
; (pk-binding-set-meta self new-value)  ; rulebook
;
; (pk-compile-fork-from-op op-compiler)
; (pk-staticenv-get-compile-fork self varname)  ; rulebook
; (pk-staticenv-default-op-compiler self)       ; rulebook
; (pk-dynenv-get-binding self varname)          ; rulebook
; (pk-dynenv-get self varname)                  ; rulebook
; (pk-dynenv-get-meta self varname)             ; rulebook
; (pk-dynenv-set-binding self varname)          ; rulebook
; (pk-dynenv-unset-binding self varname)        ; rulebook
; (pk-dynenv-set self varname)                  ; rulebook
; (pk-dynenv-set-meta self varname)             ; rulebook
;
; (pk-is-simple-identifier x)
; (pk-soup-compile-tl soup staticenv)  ; rulebook
; (pk-soup-compile soup staticenv)     ; rulebook
; (pk-sip-compile self staticenv)      ; rulebook
;
; (pk-call-meta self . args)  ; rulebook
; (pk-call self . args)       ; rulebook
;
; (pk-eval-meta self dynenv)  ; rulebook
; (pk-eval self dynenv)       ; rulebook
; (pk-eval-tl self dynenv)    ; rulebook
;
; pk-replenv*                       ; value of type 'pk-ad-hoc-env
; (pkrepl (o str (errsafe:stdin)))
;
;
; Type listing:
;
; fn-input
;   rep: A function simulating a character input stream, which
;        supports the following operations:
;   rep._!ready:  Returns t if the stream is guaranteed not to block
;                 during the next peek or read attempt, or nil if no
;                 such guarantee can be made.
;   rep._!peek:   Blocks if necessary and returns the next character
;                 in the stream without consuming it. On end-of-file,
;                 this returns nil.
;   rep._!read:   Blocks if necessary and returns the next character
;                 in the stream, consuming it. On end-of-file, this
;                 returns nil.
;
; pk-soup
;   rep: A tagged proper list containing nonempty sequences (called
;        "slurps") which contain arbitrary elements (called "sips").
;        This is merely a list format which is specialized for holding
;        elements that make sense to keep in dedicated string types,
;        such as characters and bytes.
;
; pk-bracketed-soup
;   rep: A value of type 'pk-soup. This is soup which is semantically
;        understood as being the interior of a pair of brackets. It
;        often appears as a sip in another pk-bracketed-soup's soup in
;        order to represent nested brackets.
;
; pk-lambdacalc-literal
;   rep: The value for this expression to evaluate to.
;
; pk-lambdacalc-var
;   rep: A symbol representing the variable to look up in the dynamic
;        environment when evaluating this expression.
;
; pk-lambdacalc-var-meta
;   rep: A symbol representing the variable to look up in the dynamic
;        environment when evaluating this expression. This looks up
;        the 'pk-ad-hoc-meta metadata table corresponding to the
;        variable.
;
; pk-lambdacalc-set
;   rep: A list which supports the following fields:
;   rep._.0:  A symbol representing the variable to modify in the
;             dynamic environment when evaluating this expression.
;   rep._.1:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will provide the new value for the variable
;             (which will also be the result of this expression). If
;             the new value has special metadata, that metadata will
;             be ignored, and it won't even be returned by this
;             expression.
;
; pk-lambdacalc-set-meta
;   rep: A list which supports the following fields:
;   rep._.0:  A symbol representing the variable to modify in the
;             dynamic environment when evaluating this expression.
;   rep._.1:  An expression of one of the 'pk-lambdacalc-[something]
;             types, which will provide the new value for the variable
;             (which will also be the result of this expression). If
;             the new value has special metadata, that metadata will
;             be given to the variable, and it will be returned as the
;             metadata of this expression's result.
;
; pk-lambdacalc-call
;   rep: A cons cell containing the expression for the operator and a
;        proper list of expressions for the arguments, where each
;        expression is a value of one of the
;        'pk-lambdacalc-[something] types. The expressions will be
;        evaluated from first to last and called with 'pk-call.
;
; pk-lambdacalc-call-meta
;   rep: A cons cell containing the expression for the operator and a
;        proper list of expressions for the arguments, where each
;        expression is a value of one of the
;        'pk-lambdacalc-[something] types. The expressions will be
;        evaluated from first to last and called with 'pk-call-meta.
;
; pk-compile-fork
;   rep: A table which supports the following fields:
;   rep._!get:   A value which, when called using 'pk-call, accepts no
;                arguments and returns a value of one of the
;                'pk-lambdacalc-[something] types, representing an
;                expression that returns a value to be used in a
;                parent expression.
;   rep._!meta:  A value which, when called using 'pk-call, accepts no
;                arguments and returns a value of one of the
;                'pk-lambdacalc-[something] types, representing an
;                expression that returns a value to be used by a
;                top-level command interpreter.
;   rep._!op:    A value which, when called using 'pk-call or
;                'pk-call-meta, accepts this very 'pk-compile-fork
;                value (the compiled operator), a 'pk-soup value (the
;                uncompiled body), and a static environment and
;                returns a 'pk-compile-fork value representing the
;                compiled expression.
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
;
; pk-ad-hoc-binding
;   rep: A singleton list which supports getting and setting the
;        following field:
;   rep._.0:  A value of type 'pk-ad-hoc-meta, representing the
;             metadata associated with the variable represented by
;             this binding.
;
; pk-ad-hoc-env
;   rep: A table mapping bound variable names to singleton proper
;        lists containing their bindings.
;
; pk-fn-meta
;   rep: A function which returns a value of type 'pk-ad-hoc-meta.
;        This function will be called using the arguments from
;        'pk-call or 'pk-call-meta, but only 'pk-call-meta will return
;        the full command metadata.
;
; pk-ad-hoc-meta
;   rep: A table which supports the following fields:
;   rep._!result:         The value to use as the result in any
;                         context other than the top-level one. This
;                         is the only non-optional field; if this is
;                         nil, then the value used is actually nil
;                         itself.
;   rep._!action:         If present, a singleton proper list
;                         containing a Penknife value which, when
;                         called with no arguments using 'pk-call,
;                         will imperatively perform some additional
;                         action which is meant to be done after
;                         normal evaluation and before the result is
;                         written to the REPL.
;   rep._!echoless:       Any value, used as a boolean to indicate
;                         (unless it's nil) that the result should not
;                         be written to the REPL.
;   rep._!quit:           If present, a singleton proper list
;                         indicating that the Penknife REPL session
;                         should exit and return the contained value
;                         to the Arc REPL.
;   rep._!compile-fork:   If present, a singleton proper list
;                         containing a Penknife value which, when
;                         given a variable name as a string, will
;                         return the 'pk-compile-fork value to return
;                         when compiling an identification of the
;                         variable when treating an environment
;                         containing a binding with this meta-value as
;                         a static environment. If instead this is
;                         nil, then a default compile fork should be
;                         constructed according to that environment's
;                         own behavior.


(let lathe [+ lathe-dir* _ '.arc]
  (use-fromwds-as ut do.lathe!utils
                  mr do.lathe!multival/multirule
                  oc do.lathe!multival/order-contribs
                  rc do.lathe!orc/orc
                  oi do.lathe!orc/oiter
                  sn do.lathe!imp/sniff
                  jv do.lathe!imp/jvm))

(= plt sn.plt jvm jv.jvm)


(rc:ontype fn-input-ify () fn-input fn-input
  self)

(rc:ontype fn-input-ify () string string
  (fn-input-ify instring.self))

; NOTE: Rainbow doesn't even define 'peekc. That actually doesn't
; affect us yet, since we're going through low-level hoops to get
; ready-testing behavior already, but it might be good to know.
(rc:ontype fn-input-ify () input input
  (when jvm
    ; The 'errsafe here is because Jarc translates 'input values to
    ; Readers, whereas Rainbow translates them to InputStreams. After
    ; this expression, we can be sure 'self is something that can be
    ; used as a Reader--either the reader we create, or the original
    ; value of 'self.
    (errsafe:zap jvm!java-io-InputStreamReader-new self)
    ; TODO: See if PushbackReader would be better.
    (zap jvm!java-io-BufferedReader-new self))
  (annotate 'fn-input
    (fn ((o mode 'read))
      (case mode
        ready  (~~if plt  plt.char-ready?.self
                     jvm  jvm!ready.self)
        peek   (if jvm
                 (do (jvm!mark self 2)  ; TODO: See if this can be 1.
                     (do1 (caselet charcode jvm!read.self -1 nil
                            (coerce charcode 'char))
                          jvm!reset.self))
                 peekc.self)
        read   (if jvm
                 (caselet charcode jvm!read.self -1 nil
                   (coerce charcode 'char))
                 readc.self)
               (err "Illegal fn-input option.")))))


; This translates "\r\n" and "\r" sequences to "\n".
(def newline-normalizer (str)
  (zap fn-input-ify str)
  (withs (just-returned nil
          read (fn () (ut:ret char rep.str!read
                        (= just-returned (is char #\return))))
          peek (fn (blocking)
                 ; This returns a singleton list containing the next
                 ; character in the stream, ignoring any #\newline
                 ; that comes after a #\return, translating any
                 ; #\return to a #\newline, and not consuming the
                 ; resulting character. On end-of-file, this returns a
                 ; singleton list containing nil. If blocking is nil
                 ; and the wrapped stream isn't known to have a
                 ; character ready, this returns nil.
                 (catch:while (or blocking rep.str!ready)
                   (let char rep.str!peek
                     (if (case char #\newline just-returned)
                       call.read
                       (throw:list:case char #\return #\newline
                         char))))))
    (annotate 'fn-input
      (fn ((o mode 'read))
        (case mode
          ; NOTE: Jarc doesn't like ~ by itself, so we're using '~no
          ; instead of '~~ here.
          ready  (~no do.peek.nil)
          peek   do.peek.t.0
          read   (do1 do.peek.t.0 call.read)
                 (err "Illegal fn-input option."))))))

(def comment-ignorer (str)
  (zap fn-input-ify str)
  (withs (in-comment nil
          peek (fn (blocking)
                 ; This returns a singleton list containing the next
                 ; character in the stream, ignoring comments, and
                 ; without consuming that character. On end-of-file,
                 ; this returns a singleton list containing nil. If
                 ; blocking is nil and the wrapped stream isn't known
                 ; to have a character ready, this returns nil.
                 (catch:while (or blocking rep.str!ready)
                   (let char rep.str!peek
                     (when (if in-comment
                             (or no.char (pos char "\r\n"))
                             (is char #\;))
                       (zap no in-comment))
                     (if in-comment
                       rep.str!read
                       (throw list.char))))))
    (annotate 'fn-input
      (fn ((o mode 'read))
        (case mode
          ; NOTE: Jarc doesn't like ~ by itself, so we're using '~no
          ; instead of '~~ here.
          ready  (~no do.peek.nil)
          peek   do.peek.t.0
          read   (do1 do.peek.t.0 rep.str!read)
                 (err "Illegal fn-input option."))))))


(def start-word (str (o test ~whitec))
  (zap testify test)
  (zap fn-input-ify str)
  (w/outstring s
    (catch:whilet char (or rep.str!peek rep.str!read)  ; Consume EOF.
      (if do.test.char
        (throw inside.s)
        (disp rep.str!read s)))))

(def finish-bracket-word (str (o test whitec))
  (zap testify test)
  (zap fn-input-ify str)
  (annotate 'pk-soup
    (accum acc
      (with (chars (outstring) nonchars nil)
        (while:caselet char (or rep.str!peek rep.str!read) #\[
          (do rep.str!read
              (only.acc:check inside.chars ~empty)
              (= chars (outstring))
              (push (annotate 'pk-bracketed-soup finish-brackets.str)
                    nonchars))
          (if (or no.char do.test.char)
            (do (only.acc:check inside.chars ~empty)
                (.nonchars:only acc:rev)
                nil)
            (do (.nonchars:only acc:rev)
                wipe.nonchars
                (writec rep.str!read chars)
                ; NOTE: On Rainbow, 'writec returns nil rather than
                ; the character written.
                t)))))))

(def finish-brackets (str)
  (zap fn-input-ify str)
  (do1 (finish-bracket-word str #\])
       rep.str!read))


(rc:ontype orev () string string
  (tostring:down i (- len.self 1) 0
    (writec self.i)))

(rc:ontype o-ltrim ((o test whitec)) rc.list list
  (aif (pos (complement testify.test) self)
    (split self it)
    (list self nil)))

(rc:ontype o-ltrim ((o test whitec)) string string
  (aif (pos (complement testify.test) self)
    (split self it)
    (list self "")))

(rc:ontype o-ltrim ((o test whitec)) pk-soup pk-soup
  (zap rep self)
  (let margin (accum acc
                (catch:while self
                  (let (before rest) (o-ltrim pop.self test)
                    (unless oi.oempty.rest
                      (push rest self)
                      (unless oi.oempty.before
                        do.acc.before)
                      throw.nil)
                    do.acc.before)))
    (map [annotate 'pk-soup _] (list margin self))))

(rc:ontype o-rtrim ((o test whitec)) rc.list list
  (map rev (rev:o-ltrim rev.self test)))

(rc:ontype o-rtrim ((o test whitec)) string string
  (map orev (rev:o-ltrim orev.self test)))

(rc:ontype o-rtrim ((o test whitec)) pk-soup pk-soup
  (zap rev:rep self)
  (let margin (accum acc
                (catch:while self
                  (let (rest after) (o-rtrim pop.self test)
                    (unless oi.oempty.rest
                      (push rest self)
                      (unless oi.oempty.after
                        do.acc.after)
                      throw.nil)
                    do.acc.after)))
    (map [annotate 'pk-soup rev._] (list self margin))))

; This is used internally by oi!oempty.
(rc:ontype oi.olen< (number) pk-soup pk-soup
  (and (< 0 number)
       (catch:~each slurp rep.self
         (unless (oi.olen< slurp number)
           throw.nil)
         (-- number oi.olen.slurp))))

(def o-split-first-token (seq (o test whitec))
  (zap testify test)
  (let (margin rest) (o-ltrim seq test)
    (awhen (check (o-ltrim rest ~test) ~oi.oempty:car)
      (cons margin it))))

; TODO: Use this for left-associative infix syntax.
(def o-split-last-token (seq (o test whitec))
  (zap testify test)
  (let (rest margin) (o-rtrim seq test)
    (awhen (check (o-rtrim rest ~test) ~oi.oempty:cadr)
      (join it list.margin))))

(def otokens (seq (o test whitec))
  (zap testify test)
  (accum acc
    (ut:dstwhilet (margin token rest) (o-split-first-token seq test)
      do.acc.token
      (= seq rest))))


(def soup->string (soup)
  ; NOTE: On Rainbow, (apply string '("something")) and
  ; (string '("something")) don't have the same result.
  (apply string (map slurp->string rep.soup)))

(rc:ontype slurp->string () string string
  self)

(rc:ontype slurp->string () rc.list list
  (map sip->string self))

(rc:ontype sip->string () pk-bracketed-soup pk-bracketed-soup
  (+ "[" (soup->string rep.self) "]"))


(def pk-compile-literal-from-thunk (thunk staticenv)
  (let getter (memo:fn ()
                (annotate 'pk-lambdacalc-literal call.thunk))
    (annotate 'pk-compile-fork
      (obj get   getter
           meta  getter
           op    pk-staticenv-default-op-compiler.staticenv))))

(def pk-function-call-compiler (compiled-op body staticenv)
  (let compile-op-and-body (memo:fn ()
                             (cons (pk-call rep.compiled-op!get)
                               (map [pk-call:!get:rep:pk-soup-compile
                                      _ staticenv]
                                    otokens.body)))
    (annotate 'pk-compile-fork
      (obj get   (memo:fn ()
                   (annotate 'pk-lambdacalc-call
                     call.compile-op-and-body))
           meta  (memo:fn ()
                   (annotate 'pk-lambdacalc-call-meta
                     call.compile-op-and-body))
           op    pk-staticenv-default-op-compiler.staticenv))))

; TODO: Figure out a better string syntax. Currently,
; [q Hello, world!] compiles to a literal " Hello, world!", with a
; space at the beginning and everything.
(def pk-stringquote-compiler (compiled-op body staticenv)
  (pk-compile-literal-from-thunk (fn () soup->string.body) staticenv))

; We define 'compose such that [[compose a b c] d e] is compiled based
; on the compiler of "a" and a body of this format:
;
;   (annotate 'pk-soup
;     (list:list:annotate 'pk-sip-compose
;       (list (list (annotate 'pk-soup (list "b"))
;                   (annotate 'pk-soup (list "c")))
;             (annotate 'pk-soup (list " d e")))))))
;
(def pk-compose-compiler (compiled-op body staticenv)
  (withs (token-args           otokens.body
          compile-first-arg    (memo:fn ()
                                 (if token-args
                                   (pk-soup-compile car.token-args
                                                    staticenv)
                                   (pk-compile-literal-from-thunk
                                     (fn () idfn) staticenv)))
          compile-op-and-body  (memo:fn ()
                                 (map pk-call:!get:rep
                                   (cons compiled-op
                                     (when token-args
                                       (cons call.compile-first-arg
                                         (map [pk-soup-compile
                                                _ staticenv]
                                           cdr.token-args)))))))
    (annotate 'pk-compile-fork
      (obj get   (memo:fn ()
                   (annotate 'pk-lambdacalc-call
                     call.compile-op-and-body))
           meta  (memo:fn ()
                   (annotate 'pk-lambdacalc-call-meta
                     call.compile-op-and-body))
           op    (fn (compiled-op2 body2 staticenv2)
                   (let compiled-composed-op call.compile-first-arg
                     (pk-call rep.compiled-composed-op!op
                       compiled-composed-op
                       (case cdr.token-args nil body2
                         (annotate 'pk-soup
                           (list:list:annotate 'pk-sip-compose
                             (list cdr.token-args body2))))
                       staticenv2)))))))

(def pk-assign-compiler (compiled-op body staticenv)
  (let token-args otokens.body
    (unless (is len.token-args 2)
      (err "An assignment body had more than two words in it."))
    (let (var val-token) token-args
      (zap rep var)
      (unless (and single.var (isa car.var 'string)
                (pk-is-simple-identifier car.var))
        (err:+ "A name in an assignment form wasn't a simple "
               "identifier."))
      (zap sym:car var)
      (let getter (memo:fn ()
                    (annotate 'pk-lambdacalc-set
                      (list var (pk-call:!get:rep:pk-soup-compile
                                  val-token staticenv))))
        (annotate 'pk-compile-fork
          (obj get   getter
               meta  getter
               op    pk-staticenv-default-op-compiler.staticenv))))))

(def pk-assignmeta-compiler (compiled-op body staticenv)
  (let token-args otokens.body
    (unless (is len.token-args 2)
      (err "An assignment body had more than two words in it."))
    (let (var val-token) token-args
      (zap rep var)
      (unless (and single.var (isa car.var 'string)
                (pk-is-simple-identifier car.var))
        (err:+ "A name in an assignment form wasn't a simple "
               "identifier."))
      (zap sym:car var)
      (let getter (memo:fn ()
                    (annotate 'pk-lambdacalc-set-meta
                      (list var (pk-call:!meta:rep:pk-soup-compile
                                  val-token staticenv))))
        (annotate 'pk-compile-fork
          (obj get   getter
               meta  getter
               op    pk-staticenv-default-op-compiler.staticenv))))))


(mac pk-meta args
  `(annotate 'pk-ad-hoc-meta (obj ,@args)))

(def pk-make-ad-hoc-binding (value)
  (pk-make-ad-hoc-binding-meta:pk-meta result value))

(def pk-make-ad-hoc-binding-meta (value)
  (annotate 'pk-ad-hoc-binding list.value))

(rc:ontype pk-binding-get () pk-ad-hoc-binding pk-ad-hoc-binding
  (!result:rep pk-binding-get-meta.self))

(rc:ontype pk-binding-get-meta () pk-ad-hoc-binding pk-ad-hoc-binding
  rep.self.0)

(rc:ontype pk-binding-set (new-value)
             pk-ad-hoc-binding pk-ad-hoc-binding
  (pk-binding-set-meta self (pk-meta result new-value))
  new-value)

(rc:ontype pk-binding-set-meta (new-value)
             pk-ad-hoc-binding pk-ad-hoc-binding
  (= rep.self.0 new-value))


; TODO: Consider making 'pk-lambdacalc-var-binding,
; 'pk-lambdacalc-set-binding, and 'pk-lambdacalc-unset-binding
; expression types.

(def pk-compile-fork-from-op (op-compiler)
  (fn (varname)
    (annotate 'pk-compile-fork
      (obj get   (fn () (annotate 'pk-lambdacalc-var varname))
           meta  (fn () (annotate 'pk-lambdacalc-var-meta varname))
           op    op-compiler))))

(rc:ontype pk-staticenv-get-compile-fork (varname)
             pk-ad-hoc-env pk-ad-hoc-env
  (aif (aand (pk-dynenv-get-binding self varname)
             (!compile-fork:rep:pk-binding-get-meta car.it))
    (pk-call car.it varname)
    (let op-compiler pk-staticenv-default-op-compiler.self
      (pk-call pk-compile-fork-from-op.op-compiler varname))))

(rc:ontype pk-staticenv-default-op-compiler ()
             pk-ad-hoc-env pk-ad-hoc-env
  pk-function-call-compiler)

(rc:ontype pk-dynenv-get-binding (varname) pk-ad-hoc-env pk-ad-hoc-env
  rep.self.varname)

(rc:ontype pk-dynenv-get (varname) pk-ad-hoc-env pk-ad-hoc-env
  (iflet (binding) (pk-dynenv-get-binding self varname)
    pk-binding-get.binding
    (err:+ "The variable \"" varname "\" is dynamically unbound.")))

(rc:ontype pk-dynenv-get-meta (varname) pk-ad-hoc-env pk-ad-hoc-env
  (iflet (binding) (pk-dynenv-get-binding self varname)
    pk-binding-get-meta.binding
    (err:+ "The variable \"" varname "\" is dynamically unbound.")))

(rc:ontype pk-dynenv-set-binding (varname binding)
             pk-ad-hoc-env pk-ad-hoc-env
  (= rep.self.varname list.binding)
  binding)

(rc:ontype pk-dynenv-unset-binding (varname binding)
             pk-ad-hoc-env pk-ad-hoc-env
  (wipe rep.self.varname))

(rc:ontype pk-dynenv-set (varname new-value)
             pk-ad-hoc-env pk-ad-hoc-env
  (iflet (binding) (pk-dynenv-get-binding self varname)
    (pk-binding-set binding new-value)
    (do (pk-dynenv-set-binding
          self varname pk-make-ad-hoc-binding.new-value)
        new-value)))

(rc:ontype pk-dynenv-set-meta (varname new-value)
             pk-ad-hoc-env pk-ad-hoc-env
  (iflet (binding) (pk-dynenv-get-binding self varname)
    (pk-binding-set-meta binding new-value)
    (do (pk-dynenv-set-binding
          self varname pk-make-ad-hoc-binding-meta.new-value)
        new-value)))


; TODO: Figure out what condition this should really have and how it
; should relate to ssyntax.
(def pk-is-simple-identifier (x)
  (case type.x string
    (all (orf letter [pos _ "+-*/<=>"]) x)))

(mr:rule pk-soup-compile-tl (soup staticenv) one-sip
  (zap rep soup)
  (unless (and single.soup (single car.soup))
    (do.fail "The word wasn't simply a single non-character."))
  (pk-call:!meta:rep:pk-sip-compile caar.soup staticenv))

(mr:rule pk-soup-compile-tl (soup staticenv) one-word
  (zap rep soup)
  (unless (and single.soup (isa car.soup 'string)
            (pk-is-simple-identifier car.soup))
    (do.fail "The word wasn't a simple identifier name."))
  (pk-call:!meta:rep:pk-staticenv-get-compile-fork
    staticenv (sym car.soup)))

(mr:rule pk-soup-compile-tl (soup staticenv) nonnegative-integer
  (zap rep soup)
  (unless (and single.soup (isa car.soup 'string)
            (all digit car.soup))
    (do.fail "The word wasn't a nonnegative decimal integer."))
  (annotate 'pk-lambdacalc-literal
    (coerce car.soup 'int)))

(mr:rule pk-soup-compile (soup staticenv) one-sip
  (zap rep soup)
  (unless (and single.soup (single car.soup))
    (do.fail "The word wasn't simply a single non-character."))
  (pk-sip-compile caar.soup staticenv))

(mr:rule pk-soup-compile (soup staticenv) one-word
  (zap rep soup)
  (unless (and single.soup (isa car.soup 'string)
            (pk-is-simple-identifier car.soup))
    (do.fail "The word wasn't a simple identifier name."))
  (pk-staticenv-get-compile-fork staticenv (sym car.soup)))

(mr:rule pk-soup-compile (soup staticenv) nonnegative-integer
  (zap rep soup)
  (unless (and single.soup (isa car.soup 'string)
            (all digit car.soup))
    (do.fail "The word wasn't a nonnegative decimal integer."))
  (pk-compile-literal-from-thunk
    (fn () (coerce car.soup 'int)) staticenv))

(rc:ontype pk-sip-compile (staticenv)
             pk-bracketed-soup pk-bracketed-soup
  (zap rep self)
  (iflet (margin op rest) o-split-first-token.self
    (let compiled-op (pk-soup-compile op staticenv)
      (pk-call rep.compiled-op!op compiled-op rest staticenv))
    (fail "The syntax was an empty pair of brackets.")))

(rc:ontype pk-sip-compile (staticenv) pk-sip-compose pk-sip-compose
  (let (ops body) rep.self
    (iflet (first . rest) ops
      (let compiled-op (pk-soup-compile first staticenv)
        (pk-call rep.compiled-op!op
          compiled-op
          (if rest
            (annotate 'pk-soup
              (list:list:annotate 'pk-sip-compose (list rest body)))
            body)
          staticenv))
      (fail:+ "The syntax was a composition form with nothing "
              "composed."))))

; TODO: Implement 'pk-soup-compile-tl and 'pk-soup-compile for other
; kinds of soup words, and figure out whether the two will actually be
; any different. Ssyntax and data structure syntax are probably
; especially relevant here.


(rc:ontype pk-call-meta args pk-fn-meta pk-fn-meta
  (apply pk-call rep.self args))

(mr:rule pk-call-meta (op . args) default
  (pk-meta result (apply pk-call op args)))

(oc:label-prefer-labels-last pk-call-meta-default-last
  'pk-call-meta 'default)

(rc:ontype pk-call args fn fn
  (apply self args))

(rc:ontype pk-call args pk-fn-meta pk-fn-meta
  (!result:rep:apply rep.self args))


(rc:ontype pk-eval-meta (dynenv) pk-lambdacalc-call pk-lambdacalc-call
  (pk-meta result (pk-eval self dynenv)))

(rc:ontype pk-eval-meta (dynenv)
             pk-lambdacalc-call-meta pk-lambdacalc-call-meta
  (apply pk-call-meta (accum acc
                        (each subexpr rep.self
                          (do.acc:pk-eval subexpr dynenv)))))

(rc:ontype pk-eval-meta (dynenv)
             pk-lambdacalc-literal pk-lambdacalc-literal
  (pk-meta result (pk-eval self dynenv)))

(rc:ontype pk-eval-meta (dynenv) pk-lambdacalc-var pk-lambdacalc-var
  (pk-meta result (pk-eval self dynenv)))

(rc:ontype pk-eval-meta (dynenv)
             pk-lambdacalc-var-meta pk-lambdacalc-var-meta
  (pk-dynenv-get-meta dynenv rep.self))

(rc:ontype pk-eval-meta (dynenv) pk-lambdacalc-set pk-lambdacalc-set
  (pk-meta result (pk-eval self dynenv)))

(rc:ontype pk-eval-meta (dynenv)
             pk-lambdacalc-set-meta pk-lambdacalc-set-meta
  (pk-dynenv-set-meta
    dynenv rep.self.0 (pk-eval-meta rep.self.1 dynenv)))

(rc:ontype pk-eval-meta (dynenv) pk-compile-fork pk-compile-fork
  (pk-eval-meta (pk-call rep.self!meta) dynenv))

(rc:ontype pk-eval-meta (env) pk-soup pk-soup
  (pk-eval-meta (pk-soup-compile self env) env))

(rc:ontype pk-eval (dynenv) pk-lambdacalc-call pk-lambdacalc-call
  (apply pk-call (accum acc
                   (each subexpr rep.self
                     (do.acc:pk-eval subexpr dynenv)))))

(rc:ontype pk-eval (dynenv)
             pk-lambdacalc-call-meta pk-lambdacalc-call-meta
  (!result:rep:pk-eval-meta self dynenv))

(rc:ontype pk-eval (dynenv)
             pk-lambdacalc-literal pk-lambdacalc-literal
  rep.self)

(rc:ontype pk-eval (dynenv) pk-lambdacalc-var pk-lambdacalc-var
  (pk-dynenv-get dynenv rep.self))

(rc:ontype pk-eval (dynenv)
             pk-lambdacalc-var-meta pk-lambdacalc-var-meta
  (!result:rep:pk-eval-meta self dynenv))

(rc:ontype pk-eval (dynenv) pk-lambdacalc-set pk-lambdacalc-set
  (pk-dynenv-set dynenv rep.self.0 (pk-eval rep.self.1 dynenv)))

(rc:ontype pk-eval (dynenv)
             pk-lambdacalc-set-meta pk-lambdacalc-set-meta
  (!result:rep:pk-eval-meta self dynenv))

(rc:ontype pk-eval (dynenv) pk-compile-fork pk-compile-fork
  (pk-eval (pk-call rep.self!get) dynenv))

(rc:ontype pk-eval (env) pk-soup pk-soup
  (pk-eval (pk-soup-compile self env) env))

(rc:ontype pk-eval-tl (env) pk-soup pk-soup
  (pk-eval-meta (pk-soup-compile-tl self env) env))

; TODO: Implement 'pk-eval-meta and 'pk-eval for other kinds of
; Penknife "lambdacalc" syntax, namely lambdas.


; TODO: Figure out how global environments are going to work when
; loading from files.
;
; TODO: Put more functionality in here.
;
(= pk-replenv* (annotate 'pk-ad-hoc-env (table)))

(pk-dynenv-set pk-replenv* 'demo (fn () (prn "This is a demo.")))

(pk-dynenv-set pk-replenv* '+ +)

(pk-dynenv-set pk-replenv* 'drop (annotate 'pk-fn-meta
                                   (fn ((o code 'goodbye))
                                     (pk-meta echoless  t
                                              quit      list.code))))

(pk-dynenv-set-meta pk-replenv* 'compose
  (pk-meta result        (fn args
                           (if no.args idfn
                             (let (last . rest) rev.args
                               (zap rev rest)
                               (fn args
                                 (ut.foldr pk-call
                                           (apply pk-call last args)
                                           rest)))))
           compile-fork  (list:pk-compile-fork-from-op
                           pk-compose-compiler)))

(pk-dynenv-set-meta pk-replenv* 'q
  (pk-meta result        idfn
           compile-fork  (list:pk-compile-fork-from-op
                           pk-stringquote-compiler)))

(pk-dynenv-set-meta pk-replenv* 'help
  (pk-meta echoless  t
           action    (list:fn ()
                       (prn "To exit Penknife, use \"[drop]\", "
                            "without the quotes."))))

(pk-dynenv-set-meta pk-replenv* 'assign
  (pk-meta compile-fork  (list:pk-compile-fork-from-op
                           pk-assign-compiler)))

(pk-dynenv-set-meta pk-replenv* 'assign-meta
  (pk-meta compile-fork  (list:pk-compile-fork-from-op
                           pk-assignmeta-compiler)))


; NOTE: On Rainbow, (stdin), of all things, produces an error. When
; that happens, we go get it ourselves.
(def pkrepl ((o str (errsafe:stdin)))
  (when (and no.str jv.jclass!rainbow-functions-IO)
    (= str (jvm!rainbow-functions-IO-stdIn)))
  (zap newline-normalizer:fn-input-ify str)
  ; NOTE: Jarc's 'on-err suppresses escape continuations, so
  ; 'catch:while:on-err and 'throw would fail here.
  (car:catch:until:only.throw:on-err [do (prn "Error: " details._)
                                         nil]
    (fn ()
      (unless (when rep.str!ready
                ; Shave off any newline remaining from the last input.
                ; Thanks to the fact that we're using
                ; 'newline-normalizer, we don't have to worry about
                ; "\r" and "\r\n" sequences.
                (case rep.str!peek #\newline
                  rep.str!read)
                rep.str!ready)
        (pr "pk> "))
      (aif (start-word&finish-bracket-word comment-ignorer.str)
        (let meta (pk-eval-tl it pk-replenv*)
          (awhen rep.meta!action
            (pk-call car.it))
          (unless rep.meta!echoless
            (write rep.meta!result)
            (prn))
          (whenlet (quit) rep.meta!quit
            list.quit))
        list!goodbye))))
