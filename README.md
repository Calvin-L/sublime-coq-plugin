# Sublime-Coq

This package provides Coq syntax highlighting and an interactive coqtop plugin for Coq in Sublime Text 3 & 4.  The plugin supports Coq versions 8.11 to 8.20.

I have been maintaining this plugin since 2014.  It has some advantages and disadvantages compared to the [community-supported Coq plugin](https://packagecontrol.io/packages/Coq) that you will find in Sublime's Package Control.  The main advantage is that Coq processing happens off the main thread, making the plugin much snappier.  I also regularly test support for all the versions of Coq this plugin claims to support.

## Install

There is [a different sublime-coq plugin](https://packagecontrol.io/packages/Coq) in [Package Control](https://sublime.wbond.net/). That is NOT this one. This one is different.

```
cd 'sublime-text-folder/Packages'
git clone https://github.com/Calvin-L/sublime-coq-plugin.git
```

You can find the `sublime-text-folder/Packages` folder from Sublime Text by going to Preferences -> Browse Packages.

NOTE: This plugin expects to be in a folder named `sublime-coq-plugin` in your packages folder.  The plugin will still work if you rename the folder, but the menu entries to open the settings and keyboard mappings may not work properly.

### Configuration (optional)

You may need to tell the plugin where to find Coq on your system.  Modify your plugin-specific user settings (Preferences -> Package Settings -> CoqInteractive -> Settings--User).  You should copy and modify settings from the default file (Preferences -> Package Settings -> CoqInteractive -> Settings--Default).

[Projects](https://www.sublimetext.com/docs/projects.html) can override the plugin settings.  This is especially useful if a project needs a specific version of Coq from an [Opam switch](https://opam.ocaml.org/doc/man/opam-switch.html).  To add a project-specific override, add a `"settings"` section to the project's `.sublime-project` file and prefix the plugin settings with "`coq.`".  For example, a `.sublime-project` file might look like:

```json
{
  "folders": [
    // ...
  ],
  "settings": {
    "coq.coq_install_dir": "/path/to/coq",
  }
}
```

## Usage

```
ctrl+enter: evaluate to (or rewind to) the current cursor
shift+ctrl+k: kill coqtop
```

### Secret commands

This plugin provides some fine-grained CoqIDE-style seek commands that are not bound to keys by default:
  - `coq_seek_next`: evaluate the next command
  - `coq_seek_prev`: rewind the previous command
  - `coq_seek_end`: evaluate the entire file
  - `coq_seek_start`: rewind to the start of the file

To use these commands, bind them to keystrokes by putting a keystroke configuration into the plugin key bindings (Preferences -> Package Settings -> CoqInteractive -> Key Bindings--User).  For example:
```json
[
    { "keys": ["ctrl+option+down"], "command": "coq_seek_next" },
    { "keys": ["ctrl+option+up"], "command": "coq_seek_prev" },
    { "keys": ["ctrl+option+right"], "command": "coq_seek_end" },
    { "keys": ["ctrl+option+left"], "command": "coq_seek_start" }
]
```

## Compatibility with different versions of Coq

I regularly test support for Coq versions 8.11 to 8.20.  In addition,
 - The Coq API has crystallized, so future releases of Coq are likely to work
   as well.
 - I believe that the plugin should work with Coq versions back to 8.5.  I used
   to test support for versions going back to 8.5, but it is increasingly hard
   to get these very old versions to run on new hardware.
 - Coq 8.4 and earlier are not compatible.  While 8.4 was the latest release
   when I started writing this plugin, 8.5 introduced some major breaking
   changes to the API.

## Known Issues / TODO

 - Custom notations using the `.` symbol cause problems
 - Behavior is weird and undefined when the file you are interacting with is
   re-loaded because it changed on disk
 - Sublime Text 2 is not supported (and never will be)
 - The current goal takes a long time to display when there are many goals, even if the current goal is very small
 - The plugin listens to every text change on every buffer whether or not Coq is running.  The performance impact should be negligible.  See [Issue 9](https://github.com/Calvin-L/sublime-coq-plugin/issues/9) for a longer description.
