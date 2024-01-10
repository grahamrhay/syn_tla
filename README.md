# It's a Syn!

## Run the model

```
docker run --rm -it -v $PWD:/app -w /app amazoncorretto:8-alpine3.17-jdk java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -config syn.cfg -workers auto -cleanup syn.tla
```
