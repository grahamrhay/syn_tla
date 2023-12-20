# It's a Syn!

## Run the model

```
docker run --rm -it -v $PWD:/app -w /app openjdk:14-jdk-alpine java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config syn.cfg -workers auto -cleanup syn.tla
```
