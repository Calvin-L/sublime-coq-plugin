# Sublime-Coq

This package provides Coq syntax highlighting and an interactive coqtop plugin for Coq 8.4 and Sublime Text 3. (I guess it might work with Sublime Text 2, but I haven't tested it and I don't recommend trying it.)

## Install

There is [a different sublime-coq plugin](https://github.com/mkolosick/Sublime-Coq) in [Package Control](https://sublime.wbond.net/). That is NOT this one. This one is better. Even if it does have some problems (see "Known Issues" below).

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

## Coloring

By default, the "TODO" section is colored by scope "meta.coq.todo" and the "DONE" section is colored by scope "meta.coq.proven". To actually see these regions, modify your color scheme file like so:

```
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>name</key>
    <string>(name for your color scheme)</string>
    <key>settings</key>
    <array>

        <!-- ########## BEGIN ADDITIONS -->

        <dict>
            <key>name</key>
            <string>Coq TODO</string>
            <key>scope</key>
            <string>meta.coq.todo</string>
            <key>settings</key>
            <dict>
                <key>background</key>
                <string>#563A28</string>
            </dict>
        </dict>

        <dict>
            <key>name</key>
            <string>Coq high-water mark</string>
            <key>scope</key>
            <string>meta.coq.proven</string>
            <key>settings</key>
            <dict>
                <key>background</key>
                <string>#365A28</string>
            </dict>
        </dict>

        <!-- ########## END ADDITIONS -->
```

(Of course, you may want to change the style settings to match your color scheme and taste.)

Modifying your color scheme isn't terribly easy; I'm just going to point you at [this StackOverflow question](https://stackoverflow.com/questions/18746993/how-do-i-edit-the-solarized-light-theme-in-sublime-text-3) and let you figure out the rest.

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
