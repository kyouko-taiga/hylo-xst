# Compiler tests

This directory contains tests running the entire compiler on program inputs.
Test suites are generated with the contents of the `negative` and `positive` sub-directories, which define use cases.
A use case is either a single Hylo source file or a directory representing a package.

A single-file test is compiled to a binary executable, just as if it was passed as an argument to `hc`.
A package test is built according to the configuration specified by its manifest.

## Generating Swift tests

You can use the following script to generate a XCTest method for each compiler test.

```bash
./Tools/generate-compiler-tests.swift
``` 

The script will go over each file or sub-directory under `negative` and `positive` and create a corresponding method to invoke `CompilerTests.compile(_:)`.

## Testing without the standard library

You can add `//! no-std` on the first line of a single-file test to disable the loading of the standard library.
