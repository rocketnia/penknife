# Penknife Mk. I

[![CI](https://github.com/rocketnia/penknife/actions/workflows/ci.yml/badge.svg)](https://github.com/rocketnia/penknife/actions/workflows/ci.yml)

> ℹ️ If you're here, you might be interested in the newest incarnation of Penknife, which is in the [Era](https://github.com/era-platform/era) repository.

This implements the Penknife Mk. I programming language, a [Blade](https://github.com/rocketnia/blade)-like scripting language (which may mean nothing to you, since Blade is a vaporware hobby project ^\_^ ). Penknife, like Blade, is a language that emphasizes the use of whatever syntaxes the programmer finds best in every situation.

Unlike Blade, which statically compiles a directory structure, delaying compilation of certain declarations until the necessary syntaxes are known, Penknife interprets an ongoing character stream, invoking imperative commands one at a time to build up its definition space. This makes it suitable as a REPL language.

Penknife, like Blade, emphasizes a programming style by which convenient sub-languages are developed first, and then they're used to build data structures that are compiled into whatever performant or rigorous forms are necessary. A Penknife program may indeed have some behaviors in common with a build script, making system calls to invoke machine code compilers, archival utilities, documentation generators, and so forth—but without necessarily having any non-Penknife code in the project, instead generating that code as part of the build process.


## Installation and use

Penknife Mk. I mainly just has a REPL for now. Some functionality is available at the REPL, but not much.

```racket
pk> [+ arc["Hello, "] arc["world!"]]
"Hello, world!"
```

You can then use Ctrl+C or Ctrl+D to exit.

More functionality is available by installing it as an Arc library. For instance, the Arc function `(pkrepl)` starts a Penknife REPL, and `(pkrepl "...")` executes the given code as though it were entered at the REPL.


### Using npm

Penknife Mk. I is available as an npm package. This may make it easier to install it and automate its usage, despite the fact that it isn't a JavaScript library. (There is no `require("penknife-lang")` functionality.)

The quickest way to try Penknife is using `npx`. If you have Node.js installed, you can currently fetch Penknife Mk. I and run its REPL like so at the command line:

```
npx penknife-lang run
```

If you'd like to install Penknife and use it repeatedly, you can install it globally:

```
npm install --global penknife-lang
penknife-lang run
```

For more access to the functionality exposed to Arc, the command `penknife-lang copy-into <path>` copies Penknife's Arc and Penknife source files into the directory at the given file path. This can be combined with the CLI functionality of [Rainbow.js](https://github.com/arclanguage/rainbow-js) and [Framewarc](https://github.com/rocketnia/framewarc) to build a host directory with Rainbow.js's core Arc libraries, Framewarc, and Penknife all in suitable places:

```bash
npm install --global rainbow-js-arc
npm install --global framewarc

rainbow-js-arc init-arc my-arc-host-dir/
framewarc copy-into my-arc-host-dir/lib/framewarc/
penknife-lang copy-into my-arc-host-dir/lib/penknife/
```

Once you have these files in place, run Arc:

```bash
cd my-arc-host-dir/
rainbow-js-arc run-compat
```

And at the Arc REPL, load Framewarc and Penknife like so:

```racket
(= fwarc-dir* "my/path/to/framewarc/arc/")
(load:+ fwarc-dir* "loadfirst.arc")
(= penknife-dir* "my/path/to/penknife/")
(load:+ penknife-dir* "penknife.arc")
```

Then you can run `(pkrepl)`.

This can be automated by passing command line arguments to `rainbow-js-arc run-compat`:

```racket
rainbow-js-arc run-compat \
    -e \
        '(= fwarc-dir* "lib/framewarc/")' \
        '(load:+ fwarc-dir* "loadfirst.arc")' \
        '(= penknife-dir* "lib/penknife/")' \
        '(load:+ penknife-dir* "penknife.arc")' \
        '(pkrepl)' \
    -q
```

If you'd just like to use Penknife from your own package.json file's testing scripts, you don't need to install it globally. You can run the following command to add it to your `devDependencies`:

```bash
npm install --save-dev penknife-lang
```

### As a portable Arc library

Penknife Mk. I isn't just an npm package. It's a library for Arc. It's written using [Framewarc](https://github.com/rocketnia/framewarc) in a way that's portable across multiple Arc implementations.

The implementation used by the `penknife-lang run` command is [Rainbow.js](https://github.com/arclanguage/rainbow-js). Other implementations that should work include official Arc (available via the [Anarki](https://arclanguage.github.io/) `official` branch), [Anarki](https://arclanguage.github.io/), [Jarc](http://jarc.sourceforge.net/), and [Rainbow](https://github.com/conanite/rainbow).

Note that Penknife is currently very slow on Jarc 17. This likely has to do with the way Penknife uses frequent JVM reflection on that platform.

On all these Arc implementations, it's necessary to load Framewarc before loading Penknife. Framewarc can be loaded like so:

```racket
(= fwarc-dir* "my/path/to/framewarc/arc/")
(load:+ fwarc-dir* "loadfirst.arc")
```

The main entrypoint of the Penknife library is penknife.arc. Set the global variable `penknife-dir*` before loading it, like so:

```racket
(= penknife-dir* "my/path/to/penknife/")
(load:+ penknife-dir* "penknife.arc")
```

Don't omit the trailing slashes on the paths. The `+` operation just does string concatenation, so it won't insert a slash automatically.

Once the library is loaded, you can use `(pkrepl)` to get to a Penknife REPL.

```racket
arc> (pkrepl)
pk> [+ arc["Hello, "] arc["world!"]]
"Hello, world!"
```

You can then use Ctrl+C or Ctrl+D to exit.
