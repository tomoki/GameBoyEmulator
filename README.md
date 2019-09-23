# References

- http://imrannazar.com/GameBoy-Emulation-in-JavaScript:-The-CPU
- http://gbdev.gg8.se/files/roms/blargg-gb-tests/
- http://www.pastraiser.com/cpu/gameboy/gameboy_opcodes.html
- http://bgb.bircd.org/pandocs.htm
- http://marc.rawer.de/Gameboy/Docs/GBCPUman.pdf
- https://gist.github.com/drhelius/6063288
- https://rednex.github.io/rgbds/gbz80.7.html
- 

# How to debug (on Windows)

Run in powershell

```
explorer $(rustc --print sysroot)\lib\rustlib\etc
explorer $env:USERPROFILE\.vscode\extensions\ms-vscode.cpptools-0.26.1\debugAdapters\vsdbg\bin\Visualizers
```

Copy `*.natvis` files to `%USERPROFILE%\.vscode\extensions\ms-vscode.cpptools-0.26.1\debugAdapters\vsdbg\bin\Visualizers`
