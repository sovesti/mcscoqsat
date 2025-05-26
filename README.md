# mcscoqsat

Coq-certified SAT solver extracted into Haskell

### Prerequisites

- Haskell ```stack``` - https://docs.haskellstack.org/en/stable/install_and_upgrade/
- Coq Platform - https://rocq-prover.org/doc/v8.17/refman/practical-tools/utilities.html

### Docker

```
docker build -t coqsat .
docker run --rm -it --entrypoint bash coqsat
cd mcscoqsat
stack run
```
