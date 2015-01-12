@echo off

setlocal


echo building
rem cargo build racc
set RUST_LOG=
rustc C:\src\racc\src\lib.rs --crate-name racc --crate-type dylib -g -C metadata=c775cd79df35a5d3 -C extra-filename=-c775cd79df35a5d3 --out-dir C:\src\racc\target --emit=dep-info,link -L C:\src\racc\target -L C:\src\racc\target\deps
if errorlevel 1 (
    echo build failed.
    exit /b 1
)

echo building testg
set RUST_LOG=racc=debug
rustc C:\src\racc\src\bin\testg.rs --crate-name testg --crate-type bin -g --out-dir C:\src\racc\target --emit=dep-info,link -L C:\src\racc\target -L C:\src\racc\target\deps --extern racc=C:\src\racc\target/racc-c775cd79df35a5d3.dll >port-raw.txt 2>&1
if errorlevel 1 exit /b 1

rem echo testing
rem set RUST_LOG=debug
rem target\testg >port-raw.txt 2>&1
rem if errorlevel 1 exit /b 1

echo filtering
perl filter-trace.pl <port-raw.txt >port.txt

echo running c++ reference code
orig\debug\yacc_orig.exe temp\test.y
if errorlevel 1 exit /b 1

echo windiffing
windiff trace.txt port.txt
