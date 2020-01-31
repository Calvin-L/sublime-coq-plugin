# Sublime-Coq

This package provides Coq syntax highlighting and an interactive coqtop plugin for Coq in Sublime Text 3.  The plugin supports Coq versions 8.5 to 8.10.  (It may also support higher versions, but as of this writing 8.10 is the latest.)

## Install

There is [a different sublime-coq plugin](https://packagecontrol.io/packages/Coq) in [Package Control](https://sublime.wbond.net/). That is NOT this one. This one is different.

```
cd 'sublime-text-folder/Packages'
git clone https://github.com/Calvin-L/sublime-coq-plugin.git
```

You can find the `sublime-text-folder/Packages` folder from Sublime Text by going to Preferences -> Browse Packages.

NOTE: This plugin expects to be in a folder named `sublime-coq-plugin` in your packages folder.  The plugin will still work if you rename the folder, but the menu entries to open the settings and keyboard mappings may not work properly.

You may need to tell the plugin where to find Coq on your system.  Modify your plugin-specific user settings (Preferences -> Package Settings -> CoqInteractive -> Settings--User).  You should copy and modify settings from the default file (Preferences -> Package Settings -> CoqInteractive -> Settings--Default).

## Usage

```
ctrl+enter: evaluate to (or rewind to) the current cursor
shift+ctrl+k: kill coqtop
```

## Known Issues / TODO

 - The highlighting for the proven region is really ugly. (I want some way of highlighting that colors the background without removing other syntax highlighting, but that doesn't seem possible in Sublime.)
 - Custom notations using the `.` symbol cause problems
 - I have no idea what happens if you duplicate the view in which you are interacting with Coq
 - Sublime Text 2 is not supported
