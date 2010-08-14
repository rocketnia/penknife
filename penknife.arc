; penknife.arc
;
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
; (soup-split-ltrim soup (o test whitec))
; (soup-split-first-token soup (o test whitec))
; (soup-tokens soup (o test whitec))
;
; (soup->string soup)
; (slurp->string self)  ; rulebook
;
; (pk-function-call-compiler compiled-op body staticenv)
; (pk-stringquote-compiler compiled-op body staticenv)
; (pk-compose-compiler compiled-op body staticenv)
;
; (pk-compile-fork-from-op op-compiler)
; (pk-staticenv-get-compile-fork self varname)  ; rulebook
; (pk-staticenv-default-op-compiler self)       ; rulebook
; (pk-dynenv-get self varname)                  ; rulebook
; (pk-dynenv-get-tl self varname)               ; rulebook
;
; (pk-is-simple-identifier x)
; (pk-soup-compile-tl soup staticenv)    ; rulebook
; (pk-soup-compile soup staticenv)       ; rulebook
; (pk-slurp-compile brackets staticenv)  ; rulebook
;
; (pk-call-tl self . args)  ; rulebook
; (pk-call self . args)     ; rulebook
;
; (pk-eval-tl self dynenv)  ; rulebook
; (pk-eval self dynenv)     ; rulebook
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
;   rep: A tagged proper list containing strings and proper lists of
;        non-characters. This is merely a list format which is
;        specialized for representing contiguous stretches of
;        characters as strings internally. An element of a pk-soup is
;        called a "slurp".
;
; pk-bracketed-soup
;   rep: A value of type 'pk-soup. This is soup which is semantically
;        understood as being the interior of a pair of brackets. It
;        often appears as a slurp in another pk-bracketed-soup's soup
;        in order to represent nested brackets.
;
; pk-lambdacalc-literal
;   rep: The value for this expression to evaluate to.
;
; pk-lambdacalc-var
;   rep: A symbol representing the variable to look up in the dynamic
;        environment when evaluating this expression.
;
; pk-lambdacalc-var-tl
;   rep: A symbol representing the variable to look up in the dynamic
;        environment when evaluating this expression. This looks up
;        any metadata which is associated to the variable so that the
;        variable name can be used as a top-level command.
;
; pk-lambdacalc-call
;   rep: A cons cell containing the expression for the operator and a
;        proper list of expressions for the arguments, where each
;        expression is a value of one of the
;        'pk-lambdacalc-[something] types. The expressions will be
;        evaluated from first to last and called with 'pk-call.
;
; pk-lambdacalc-call-tl
;   rep: A cons cell containing the expression for the operator and a
;        proper list of expressions for the arguments, where each
;        expression is a value of one of the
;        'pk-lambdacalc-[something] types. The expressions will be
;        evaluated from first to last and called with 'pk-call-tl.
;
; pk-compile-fork
;   rep: A table which contains the following fields:
;   rep._!get:  A value which, when called using 'pk-call, accepts no
;               arguments and returns a value of one of the
;               'pk-lambdacalc-[something] types, representing an
;               expression that returns a value to be used in a parent
;               expression.
;   rep._!tl:   A value which, when called using 'pk-call, accepts no
;               arguments and returns a value of one of the
;               'pk-lambdacalc-[something] types, representing an
;               expression that returns a value to be used by a
;               top-level command interpreter.
;   rep._!op:   A value which, when called using 'pk-call or
;               'pk-call-tl, accepts this very 'pk-compile-fork value
;               (the compiled operator), a 'pk-soup value (the
;               uncompiled body), and a static environment and returns
;               a 'pk-compile-fork value representing the compiled
;               expression.
;
; pk-slurp-compose
;   rep: A list which contains the following fields:
;   rep._.0:  A nonempty proper list of 'pk-soup values representing
;             uncompiled operator expressions to apply in reverse
;             order, in series, to the body. If there is only one
;             operator, it will be applied to the body directly.
;             Otherwise, the first operator will be applied to a
;             new 'pk-slurp-compose value containing the rest of the
;             composition information.
;   rep._.1:  A 'pk-soup value representing the uncompiled body to
;             apply the operators to.
;
; pk-ad-hoc-env
;   rep: A table mapping bound variable names to tables which support
;        the following fields:
;   rep._.name!value:         The value to return when looking up the
;                             variable's value when treating this as a
;                             dynamic environment.
;   rep._.name!tl-value:      If present, the table to return when
;                             looking up the variable's top-level
;                             command metadata when treating this as a
;                             dynamic environment. (The top-level
;                             command metadata is used by the command
;                             interpreter when the variable name is
;                             all there is to the command.) If instead
;                             this is nil, then a default metadata
;                             table will be constructed, wrapping the
;                             variable's value.
;   rep._.name!compile-fork:  If present, a singleton proper list
;                             containing a Penknife value which, when
;                             given the variable name as a string,
;                             will return the 'pk-compile-fork value
;                             to return when compiling an
;                             identification of the variable when
;                             treating this as a static environment.
;                             If instead this is nil, then a default
;                             'pk-compile-fork will be constructed.
;
; pk-tl-fn
;   rep: A function which returns a top-level command metadata table.
;        This function will be called using the arguments from
;        'pk-call or 'pk-call-tl, but only 'pk-call-tl will return the
;        full command metadata.
;
; Top-level command metadata table
;   This is not a tagged type. Instead, it's a table which supports
;   the following fields:
;     _!result:    The value to use as the result in any context other
;                  than the top-level one. This is the only
;                  non-optional field; if this is nil, then the value
;                  used is actually nil itself.
;     _!action:    If present, a singleton proper list containing a
;                  Penknife value which, when called with no arguments
;                  using 'pk-call, will imperatively perform some
;                  additional action which is meant to be done after
;                  normal evaluation and before the result is written
;                  to the REPL.
;     _!echoless:  Any value, used as a boolean to indicate (unless
;                  it's nil) that the result should not be written to
;                  the REPL.
;     _!quit:      If present, a singleton proper list indicating that
;                  the Penknife REPL session should exit and return
;                  the contained value to the Arc REPL.


(let lathe [+ lathe-dir* _ '.arc]
  (use-fromwds-as ut do.lathe!utils
                  mr do.lathe!multival/multirule
                  oc do.lathe!multival/order-contribs
                  rc do.lathe!orc/orc
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


(def soup-split-ltrim (soup (o test whitec))
  (zap rep soup)
  (zap complement:testify test)
  (let prefix (accum acc
                (catch:while soup
                  (let slurp pop.soup
                    (only.throw:awhen (pos test slurp)
                      (let (firstpart rest) (split slurp it)
                        (push rest soup)
                        (case it 0 t
                          do.acc.firstpart)))
                    do.acc.slurp)))
    (map [annotate 'pk-soup _] (list prefix soup))))

(def soup-split-first-token (soup (o test whitec))
  (zap testify test)
  (let (_ trimmed) (soup-split-ltrim soup test)
    (check (soup-split-ltrim trimmed ~test) rep:car)))

(def soup-tokens (soup (o test whitec))
  (zap testify test)
  (accum acc
    (ut:dstwhilet (token rest) (soup-split-first-token soup test)
      do.acc.token
      (= soup rest))))


(def soup->string (soup)
  ; NOTE: On Rainbow, (apply string '("something")) and
  ; (string '("something")) don't have the same result.
  (apply string
    (map [case type._ string _ (map slurp->string _)] rep.soup)))

(rc:ontype slurp->string () pk-bracketed-soup pk-bracketed-soup
  (+ "[" (soup->string rep.self) "]"))


(def pk-function-call-compiler (compiled-op body staticenv)
  (let compile-op-and-body (memo:fn ()
                             (cons (pk-call rep.compiled-op!get)
                               (map [pk-call:!get:rep:pk-soup-compile
                                      _ staticenv]
                                    soup-tokens.body)))
    (annotate 'pk-compile-fork
      (obj get  (memo:fn ()
                  (annotate 'pk-lambdacalc-call
                    call.compile-op-and-body))
           tl   (memo:fn ()
                  (annotate 'pk-lambdacalc-call-tl
                    call.compile-op-and-body))
           op   pk-staticenv-default-op-compiler.staticenv))))

; TODO: Figure out a better string syntax. Currently,
; [q Hello, world!] compiles to a literal " Hello, world!", with a
; space at the beginning and everything.
(def pk-stringquote-compiler (compiled-op body staticenv)
  (let getter (memo:fn ()
                (annotate 'pk-lambdacalc-literal soup->string.body))
    (annotate 'pk-compile-fork
      (obj get  getter
           tl   getter
           op   pk-staticenv-default-op-compiler.staticenv))))

; We define 'compose such that [[compose a b c] d e] is compiled based
; on the compiler of "a" and a body of this format:
;
;   (annotate 'pk-soup
;     (list:list:annotate 'pk-slurp-compose
;       (list (list (annotate 'pk-soup (list "b"))
;                   (annotate 'pk-soup (list "c")))
;             (annotate 'pk-soup (list " d e")))))))
;
(def pk-compose-compiler (compiled-op body staticenv)
  (withs (token-args           soup-tokens.body
          compile-first-arg    (when token-args
                                 (memo:fn ()
                                   (pk-soup-compile car.token-args
                                                    staticenv)))
          compile-op-and-body  (memo:fn ()
                                 (map pk-call:!get:rep
                                   (cons compiled-op
                                     (when token-args
                                       (cons call.compile-first-arg
                                         (map [pk-soup-compile
                                                _ staticenv]
                                           cdr.token-args)))))))
    (annotate 'pk-compile-fork
      (obj get  (memo:fn ()
                  (annotate 'pk-lambdacalc-call
                    call.compile-op-and-body))
           tl   (memo:fn ()
                  (annotate 'pk-lambdacalc-call-tl
                    call.compile-op-and-body))
           op   (fn (compiled-op2 body2 staticenv2)
                  (unless token-args
                    (err:+ "A 'compose form with no arguments was "
                           "used in functional position."))
                  (let compiled-composed-op call.compile-first-arg
                    (pk-call rep.compiled-composed-op!op
                      compiled-composed-op
                      (if single.token-args body2
                        (annotate 'pk-soup
                          (list:list:annotate 'pk-slurp-compose
                            (list cdr.token-args body2))))
                      staticenv2)))))))


(def pk-compile-fork-from-op (op-compiler)
  (fn (varname)
    (annotate 'pk-compile-fork
      (obj get  (fn () (annotate 'pk-lambdacalc-var varname))
           tl   (fn () (annotate 'pk-lambdacalc-var-tl varname))
           op   op-compiler))))

(rc:ontype pk-staticenv-get-compile-fork (varname)
             pk-ad-hoc-env pk-ad-hoc-env
  (aif (aand rep.self.varname it!compile-fork)
    (pk-call car.it varname)
    (let op-compiler pk-staticenv-default-op-compiler.self
      (pk-call pk-compile-fork-from-op.op-compiler varname))))

(rc:ontype pk-staticenv-default-op-compiler ()
             pk-ad-hoc-env pk-ad-hoc-env
  pk-function-call-compiler)

(rc:ontype pk-dynenv-get (varname) pk-ad-hoc-env pk-ad-hoc-env
  (!value:or rep.self.varname
    (err:+ "The variable \"" varname "\" is dynamically unbound.")))

(rc:ontype pk-dynenv-get-tl (varname) pk-ad-hoc-env pk-ad-hoc-env
  (or (!tl-value:or rep.self.varname
        (err:+ "The variable \"" varname "\" is dynamically "
               "unbound."))
      (obj result (pk-dynenv-get self varname))))


; TODO: Figure out what condition this should really have and how it
; should relate to ssyntax.
(def pk-is-simple-identifier (x)
  (case type.x string
    (all [case _ #\- t letter._] x)))

(mr:rule pk-soup-compile-tl (soup staticenv) one-slurp
  (zap rep soup)
  (unless (and single.soup (single car.soup))
    (do.fail "The word wasn't simply a single non-character."))
  (pk-call:!tl:rep:pk-slurp-compile caar.soup staticenv))

(mr:rule pk-soup-compile-tl (soup staticenv) one-word
  (zap rep soup)
  (unless (and single.soup (isa car.soup 'string)
            (pk-is-simple-identifier car.soup))
    (do.fail "The word wasn't a simple identifier name."))
  (pk-call:!tl:rep:pk-staticenv-get-compile-fork
    staticenv (sym car.soup)))

(mr:rule pk-soup-compile-tl (soup staticenv) nonnegative-integer
  (zap rep soup)
  (unless (and single.soup (isa car.soup 'string)
            (all digit car.soup))
    (do.fail "The word wasn't a nonnegative decimal integer."))
  (annotate 'pk-lambdacalc-literal
    (coerce car.soup 'int)))

(mr:rule pk-soup-compile (soup staticenv) one-slurp
  (zap rep soup)
  (unless (and single.soup (single car.soup))
    (do.fail "The word wasn't simply a single non-character."))
  (pk-slurp-compile caar.soup staticenv))

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
  (let getter (memo:fn ()
                (annotate 'pk-lambdacalc-literal
                  (coerce car.soup 'int)))
    (annotate 'pk-compile-fork
      (obj get  getter
           tl   getter
           op   pk-staticenv-default-op-compiler.staticenv))))

(rc:ontype pk-slurp-compile (staticenv)
             pk-bracketed-soup pk-bracketed-soup
  (zap rep self)
  (iflet (op rest) soup-split-first-token.self
    (let compiled-op (pk-soup-compile op staticenv)
      (pk-call rep.compiled-op!op compiled-op rest staticenv))
    (fail "The syntax was an empty pair of brackets.")))

(rc:ontype pk-slurp-compile (staticenv)
             pk-slurp-compose pk-slurp-compose
  (let (ops body) rep.self
    (iflet (first . rest) ops
      (let compiled-op (pk-soup-compile first staticenv)
        (pk-call rep.compiled-op!op
          compiled-op
          (if rest
            (annotate 'pk-soup
              (list:list:annotate 'pk-slurp-compose (list rest body)))
            body)
          staticenv))
      (fail:+ "The syntax was a composition form with nothing "
              "composed."))))

; TODO: Implement 'pk-soup-compile-tl and 'pk-soup-compile for other
; kinds of soup words, and figure out whether the two will actually be
; any different. Ssyntax and data structure syntax are probably
; especially relevant here.


(rc:ontype pk-call-tl args pk-tl-fn pk-tl-fn
  (apply pk-call rep.self args))

(mr:rule pk-call-tl (op . args) default
  (obj result (apply pk-call op args)))

(oc:label-prefer-labels-last pk-call-tl-default-last
  'pk-call-tl 'default)

(rc:ontype pk-call args fn fn
  (apply self args))

(rc:ontype pk-call args pk-tl-fn pk-tl-fn
  (!result:apply rep.self args))


(rc:ontype pk-eval-tl (dynenv) pk-lambdacalc-call pk-lambdacalc-call
  (obj result (pk-eval self dynenv)))

(rc:ontype pk-eval-tl (dynenv)
             pk-lambdacalc-call-tl pk-lambdacalc-call-tl
  (apply pk-call-tl (accum acc
                      (each subexpr rep.self
                        (do.acc:pk-eval subexpr dynenv)))))

(rc:ontype pk-eval-tl (dynenv)
             pk-lambdacalc-literal pk-lambdacalc-literal
  (obj result (pk-eval self dynenv)))

(rc:ontype pk-eval-tl (dynenv) pk-lambdacalc-var pk-lambdacalc-var
  (obj result (pk-eval self dynenv)))

(rc:ontype pk-eval-tl (dynenv)
             pk-lambdacalc-var-tl pk-lambdacalc-var-tl
  (pk-dynenv-get-tl dynenv rep.self))

(rc:ontype pk-eval-tl (dynenv) pk-compile-fork pk-compile-fork
  (pk-eval-tl (pk-call rep.self!tl) dynenv))

(rc:ontype pk-eval-tl (env) pk-soup pk-soup
  (pk-eval-tl (pk-soup-compile-tl self env) env))

(rc:ontype pk-eval (dynenv) pk-lambdacalc-call pk-lambdacalc-call
  (apply pk-call (accum acc
                   (each subexpr rep.self
                     (do.acc:pk-eval subexpr dynenv)))))

(rc:ontype pk-eval (dynenv)
             pk-lambdacalc-call-tl pk-lambdacalc-call-tl
  (!result:pk-eval-tl self dynenv))

(rc:ontype pk-eval (dynenv)
             pk-lambdacalc-literal pk-lambdacalc-literal
  rep.self)

(rc:ontype pk-eval (dynenv) pk-lambdacalc-var pk-lambdacalc-var
  (pk-dynenv-get dynenv rep.self))

(rc:ontype pk-eval (dynenv) pk-lambdacalc-var-tl pk-lambdacalc-var-tl
  (!result:pk-eval-tl self dynenv))

(rc:ontype pk-eval (dynenv) pk-compile-fork pk-compile-fork
  (pk-eval (pk-call rep.self!get) dynenv))

(rc:ontype pk-eval (env) pk-soup pk-soup
  (pk-eval (pk-soup-compile self env) env))

; TODO: Implement 'pk-eval-tl and 'pk-eval for other kinds of Penknife
; "lambdacalc" syntax, namely lambdas.


; TODO: Figure out how global environments are going to work when
; loading from files.
;
; TODO: Put more functionality in here.
;
(= pk-replenv* (annotate 'pk-ad-hoc-env
                 (obj demo     (obj value
                                 (fn () (prn "This is a demo.")))
                      plus     (obj value +)
                      drop
                        (obj value
                          (annotate 'pk-tl-fn
                            (fn ((o code 'goodbye))
                              (obj echoless t quit list.code))))
                      compose
                        (obj value
                               (fn args
                                 (if no.args idfn
                                   (let (last . rest) rev.args
                                     (zap rev rest)
                                     (fn args
                                       (ut.foldr pk-call
                                         (apply pk-call last args)
                                         rest)))))
                             compile-fork
                               (list:pk-compile-fork-from-op
                                 pk-compose-compiler))
                      q        (obj value     idfn
                                    compile-fork
                                      (list:pk-compile-fork-from-op
                                        pk-stringquote-compiler))
                      help
                        (obj tl-value
                          (obj echoless  t
                               action
                                 (list:fn ()
                                   (prn "To exit Penknife, use "
                                        "\"[drop]\", without the "
                                        "quotes.")))))))

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
        (let tl-result (pk-eval-tl it pk-replenv*)
          (awhen do.tl-result!action
            (pk-call car.it))
          (unless do.tl-result!echoless
            (write do.tl-result!result)
            (prn))
          (whenlet (quit) do.tl-result!quit
            list.quit))
        list!goodbye))))
