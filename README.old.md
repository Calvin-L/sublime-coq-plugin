# Sublime-Coq

This package provides Coq syntax highlighting and an interactive coqtop plugin for Coq in Sublime Text 3.  The plugin supports Coq versions 8.5 to 8.10.  (It may also support higher versions, but as of this writing 8.10 is the latest.)

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

 - There aren't really any settings available, so you might need to modify CoqPlugin.py on your own
 - The highlighting for the proven region is really ugly. (I want some way of highlighting that colors the background without removing other syntax highlighting, but that doesn't seem possible in Sublime.)
 - Custom notations using the `.` symbol cause problems
 - Keyboard bindings only exist for OSX
 - I have no idea what happens if you duplicate the view in which you are interacting with Coq
 - Sublime Text 2 is not supported
