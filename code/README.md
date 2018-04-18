Coupled Sim Fiddle
==================

The Coupled Sim Fiddle is a tool for playing around with labeled transition systems and algorithms on them (especially concerning coupled similarity – a notion of equivalence for systems with internal steps.)

A live instance of the tool runs on <https://coupledsim.bbisping.de>.

The repository also contains Benjamin Bisping's master's thesis "Computing coupled similarity" (in `/thesis/`).


Building the web tool
---------------------
The web tool can be built using `sbt webStage`. After that, `web/target/web/stage/index.html` contains the tool.

Tests of the algorithms on a set of transition systems are triggered by `sbt test`. (Unfortunately, the node.js integration in the project is a little unfirm. It may be that you have to manually install node.js modules for the tests to run, for example, `npm install jsdom` in the `code` directory.)

(You will need sbt. For installation instructions, go to <https://www.scala-sbt.org/download.html>.)

The Apache Flink program
------------------------
A program to compute coupled simulation reslations using Apache Flink can be used via `sbt flink/run`.

The program takes the following arguments:

Switch                   | Effect
------------------------ | --------------------------------------
--ts PATH/TO/LTS.csv     | Determine the input transition system (must be given as a CSV with format: "srcId, tarId, actionName". The internal action is denoted by "i".)
--overapproximation ARG  | Which over-approximation to apply to keep the game small. (Default: bigstep, alternative: none)
--preminimization ARG    | Which under-approximation to use for minimization at the beginning of the algorithm. (Default: delaybisim, alternative: weakbisim)
--outputgame             | Whether to write the game to disk. (Will be written to input source path with ".game" appended)
--checksoundness         | Checks that the result relation really is a coupled simulation
--parallelism N          | Degree of parallelism for the Flink program
--sizemark               | Output sizes of systems, games, results for predefined benchmark set (takes a lot of time and space)
--timemark               | Output running times for predefined benchmark set (takes a lot of time)

(Arguments are channelled through sbt like this: `sbt "flink/run --ts myTransitionSystem.csv"`)

Tests can be run by `sbt flink/test`.
