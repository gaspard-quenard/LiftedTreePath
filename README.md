# Build

```bash
./gradlew build
```

# Add the z3 API

Clone the z3 repository inside the app/libs/solvers directory:

```bash
cd app/libs/solvers
git clone 
https://github.com/Z3Prover/z3
```

Then build z3 with the java bindings:

```bash
cd z3
python scripts/mk_make.py --java
cd build
make -j 4
```

Then copy the jar file generated into the libs folder.

Finally, updatet he LD_LIBRARY_PATHto contains the build folder, so that the shared library can be loaded at runtime:

```bash
export LD_LIBRARY_PATH=/<PATH_TO_REPO>/app/libs/solvers/z3/build:$LD_LIBRARY_PATH
```

If your editor is vscode, and it indicate that "the import cannot be resolved", you can try the command:
```
Java Clean: Clean java language server workspace
```

# Run 

```bash
./gradlew run --args="-d <domain_file> -p <problem_file>"
```