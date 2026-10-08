# Editor syntax highlighting

[STN.tmbundle](STN.tmbundle) contains one shared TextMate grammar for `.stypes`
files. It assigns conventional scopes to section headers, type declarations,
traits, functions and members, finite binders, built-in types, operators,
punctuation, ordinary comments, and semantic descriptions. Your editor's color
scheme determines the colors; some themes style documentation and ordinary
comments identically.

The grammar follows the single-line declaration syntax in [doc.md](../doc.md).
Names need not start with an uppercase letter. `///` is documentation only at
the beginning of a line after optional indentation; inline `///` is an ordinary
comment. Trait fields use the same function scopes as methods.

This package provides lexical highlighting and comment toggling. Semantic name
resolution, diagnostics, completion, and navigation would require additional
editor integration, such as a language server. Continue using `stn-validator`
to validate documents.

## Sublime Text

1. Choose **Preferences → Browse Packages…**.
2. Copy the entire `STN.tmbundle` directory into the directory that opens.
3. Open a `.stypes` file. If a previously selected syntax overrides automatic
   detection, use the command palette's **Set Syntax: Semantic Types Notation**.

Sublime reads the `.tmLanguage` grammar directly; Python plugin code and Package
Control are not required. Its **Toggle Comment** command uses `//` through the
included `Comments.tmPreferences`. For updates, replace the copied bundle.

### Brighter function names in the Mariana color scheme

The default dark Mariana scheme gives function names a muted cyan color. To make
STN function and method names brighter, copy
[sublime/Mariana.sublime-color-scheme](sublime/Mariana.sublime-color-scheme) into
the `User` subdirectory of the Packages directory. Sublime merges this partial
file with the installed Mariana scheme; it changes only function and method
names in STN documents, including fields written with the method shorthand.

If `User/Mariana.sublime-color-scheme` already exists, append the supplied rule
to its `rules` array rather than replacing your customizations. The rule uses
light blue (`#8BD5FF`); you can change this color without changing the grammar.
Other color schemes need the same rule in a customization file named after
their `.sublime-color-scheme` file.

## IntelliJ IDEA

Enable the **TextMate Bundles** plugin if it is disabled. In **Settings → Editor
→ TextMate Bundles**, add the `STN.tmbundle` directory from this repository.
The bundle associates the syntax with `.stypes` files.

## Visual Studio Code

VS Code can reuse `STN.tmbundle/Syntaxes/STN.tmLanguage` unchanged, but requires
an extension manifest to register the language and grammar. For example, place
this `package.json` beside a copy of the `STN.tmbundle` directory in a local
extension directory:

```json
{
  "name": "stn-syntax",
  "displayName": "Semantic Types Notation",
  "version": "0.1.0",
  "publisher": "local",
  "engines": { "vscode": "^1.85.0" },
  "contributes": {
    "languages": [{
      "id": "stn",
      "aliases": ["Semantic Types Notation", "STN"],
      "extensions": [".stypes"]
    }],
    "grammars": [{
      "language": "stn",
      "scopeName": "source.stn",
      "path": "./STN.tmbundle/Syntaxes/STN.tmLanguage"
    }]
  }
}
```

This manifest is an integration example, not a published VS Code extension.
VS Code comment toggling also needs a language configuration with
`"comments": { "lineComment": "//" }`; it does not read TextMate preferences.

## Format and maintenance

The shared grammar is
[Syntaxes/STN.tmLanguage](STN.tmbundle/Syntaxes/STN.tmLanguage), an XML property
list with ordered regular-expression rules. At each position the first matching
rule wins, so comments, declarations, and keywords precede general type names.
Rules never retain state across lines, allowing incomplete declarations to be
edited without changing highlighting on subsequent lines.

TextMate is a widely supported grammar format, rather than a universal editor
standard. Sublime also has a richer native `.sublime-syntax` format, but STN
currently needs no editor-specific grammar features. There is no generated copy
to keep in sync.

Format and installation references:

- [Sublime syntax definitions](https://www.sublimetext.com/docs/syntax.html)
- [VS Code syntax highlight guide](https://code.visualstudio.com/api/language-extensions/syntax-highlight-guide)
- [IntelliJ IDEA TextMate bundles](https://www.jetbrains.com/help/idea/textmate.html)
