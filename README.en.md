# Model of the Android permission system

This project contains a formalization written in Coq of the Android permission system.
Our objective is to formally prove safety and security properties of the model that may be of interest to anyone that is near
the Android enviroment (i.e. both users and developers).

#### Version of Coq used to compile this project

```
The Coq Proof Assistant, version 8.11.0 (March 2020)
compiled on Mar 5 2020 20:37:30 with OCaml 4.08.1
```

## How to compile

In the root folder of the project, simply run:

```sh
cd src
./makeMakefile
make
```

## Organization of the files

### Basic definitions and model formalization

The following files are the ones that define the abstract representation of the Android permission
system.

- DefBasicas.v: contains basic definitions of the components of the Android ecosystem, such as
  intents, activities, services, content providers, etc.
- Estado.v: defines the state of our Android representation. It also defines what a valid state is.
- Operaciones.v: defines the operations that can mutate the state of the system. In other words, all of
  the allowed actions that our system can perform, are defined here.
- Semantica.v: defines the semantics of the actions mentioned above. For each one of them, we define
  a precondition and a postcondition. The file is divided into sections that correspond with the
  action's semantic we are defining.
- Exec.v: defines what a system execution is.
- ErrorManagement.v: defines the different error codes that can be obtained from an execution.

### Proof of valid state preservation among executions

One important property we proved over the above model is that its executions preservs valid states.

- ValidityInvariance.v: contains the proof that an execution in the system preserves the state
  validity. Note that we divided this proof into smaller ones by proving each action in a separate
  file. For example, for the `install` action, the file `InstallIsInvariant.v` can be found.

### Functional implementation of the model

- Implementacion.v: contains a functional implementation of our idealized model.
- Soundess.v: contains the proof that our functional implementation is sound with respect to the
  formal specification. Again, we divided this proof into smaller one by splitting it into one
  sub-proof for each action. For example, for the `grant` action (i.e. the action that grants a
  permission), the file `GrantIsSound.v` can be found.

### Other properties

- ModelProperties.v: groups all of the properties we proved about our model or out funcional
  implementation with the exception of:
  - Eavesdropping.v
  - IntentSpoofing.v
- The rest of the files, such as `RvkAndNotGrant.v`, `IfPermThenGranted.v` or
  `IfOldAppRunThenVerified.v`, contains the proof of some of the properties grouped into
  `ModelProperties.v` just for the sake of keeping each of the properties in its own file.
