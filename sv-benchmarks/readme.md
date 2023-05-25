# Set-up benchmark
1. install [benchexec](https://github.com/sosy-lab/benchexec/tree/main) using the guide on the website
2. add the toolinfo file `jip.py` to the `tools` folder of your benchexec installation
2. from a folder containing `jip.exe` run `benchexec --read-only-dir / --overlay-dir /home/ <path>/<to>/benchmarks/jip.xml`