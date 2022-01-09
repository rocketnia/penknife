#!/usr/bin/env node

import $path from "path";
import $url from "url";

import commander from "commander";
import fse from "fs-extra";

const __dirname = $path.dirname($url.fileURLToPath(import.meta.url));

const pkg = await fse.readJson($path.join(__dirname, "package.json"), "utf8");


const program = new commander.Command();
program.version(pkg.version);
program.enablePositionalOptions();

program.command("copy-into <dir>")
    .allowExcessArguments(false)
    .description(
        "copy Penknife's Arc and Penknife files into `dir`, typically " +
        "<Arc host dir>/lib/penknife/")
    .action(dir => {
        const files = [
            "penknife.arc",
            "pk-core.arc",
            "pk-hefty-fn.arc",
            "pk-modules.arc",
            "pk-qq.arc",
            "pk-thin-fn.arc",
            "pk-util.arc",
            "pk-util.pk"
        ];
        for (const file of files) {
            fse.copy($path.join(__dirname, file), $path.join(dir, file));
        }
    });

await program.parseAsync();
