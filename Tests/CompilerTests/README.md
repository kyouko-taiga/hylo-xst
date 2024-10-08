# Compiler tests

This directory contains tests running the entire compiler on program inputs.
Test suites are generated with the contents of the `negative` and `positive` sub-directories, which define use cases.
A use case is either a single Hylo source file or a directory representing a project.

## Generating Swift tests

You can use the following script to generate a XCTest method for each compiler test.

```bash
./Tools/generate-compiler-tests.swift
``` 

The script will go over each file or sub-directory under `negative` and `positive` and create a corresponding method to invoke `CompilerTests.compile(_:)`.
