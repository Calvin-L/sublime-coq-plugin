# Sublime-Coq

This package provides Coq syntax highlighting and an interactive coqtop plugin for Coq 8.6+ and Sublime Text 3. (I guess it might work with Sublime Text 2, but I haven't tested it and I don't recommend trying it.)

## Install

There is [a different sublime-coq plugin](https://packagecontrol.io/packages/Coq) in [Package Control](https://sublime.wbond.net/). That is NOT this one. This one is different.

```
cd 'sublime-text-folder/Packages'
git clone 'this-repo'
```

You can find the `sublime-text-folder/Packages` folder from Sublime Text by going to Preferences -> Browse Packages.

## Usage

```
ctrl+enter: evaluate to (or rewind to) the current cursor
shift+ctrl+k: kill coqtop
```

## Known Issues / TODO

 - Only known to work in Coq 8.6+
 - There aren't really any settings available, so you might need to modify CoqPlugin.py on your own
 - The highlighting for the proven region is really ugly. (I want some way of highlighting that colors the background without removing other syntax highlighting, but that doesn't seem possible in Sublime.)
 - Typing in the proven or TODO region can confuse the plugin
 - Comments immediately preceeding bullets (e.g. `(* hello world *) - auto.`) cause problems
 - Custom notations using the `.` symbol cause problems
 - Keyboard bindings only exist for OSX
 - High-water mark sometimes gets out of sync with reality (especially during undo)
 - Feedback from commands `Check`, `Print`, `Search`, etc. is not shown in the response window
 - I have no idea what happens if you duplicate the view in which you are interacting with Coq
