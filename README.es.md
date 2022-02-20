# Formalización del sistema de permisos de Android

Este proyecto contiene una formalización del sistema de permisos de Android escrita en Coq. El
objetivo de la misma es desarrollar un framework de trabajo que permita probar formalmente
propiededes de _safety_ y _security_ sobre Android que sean de interés tanto a usuarios como a
desarrolladores.

#### Versión de Coq usada en el proyecto

```
The Coq Proof Assistant, version 8.11.0 (March 2020)
compiled on Mar 5 2020 20:37:30 with OCaml 4.08.1
```

## Como compilar

En la carpeta raíz del proyecto, ejecutar:

```sh
./makeMakefile
make
```

## Organización de los archivos

### Definiciones básicas y formalización

Los siguientes archivos definen los componentes que conforman nuestra representación abstracta del
sistema de permisos de Android.

- DefBasicas.v: contiene definiciones básicas de las distintas partes de Android que formalizamos,
  como por ejemplo, los intents, las actividades, los servicioes y los content providers.
- Estado.v: define la estructura que tendrá estado de nuestro modelo abstracto y cuándo uno de esos
  estados será válido.
- Operaciones.v: define las acciones permitidas que pueden ser modificar el estado de nuestro modelo.
- Semantica.v: para cada una de las acciones listadas en el archivo anterior, aquí definimos su
  semántica. El archivo está dividido en secciones, correspondiéndose cada una de ellas a una acción
  en particular.
- Exec.v: contiene la definición de una "ejecución" de nuestro modelo.
- ErrorManagement.v: define los mensajes de error que pueden obtenerse en una ejecución errónea.

Una propiedad importante que probamos con respecto a nuestro modelo es que sus ejecuciones conservan
la validez del estado. Dicha prueba puede encontrarse en `ValidityInvariance.v`. Sin embargo, dicha
prueba fue subdividida en pruebas más pequeñas al probar la propiedad para cada acción por separado.
Estos sub-lemas pueden encontrarse en los archivos con el sufijo `IsInvariant`. Por ejemplo, para la
acción `install`, debemos referirnos al archivo `InstallIsInvariant.v`.

### Implementación funcional de nuestro modelo

- Implementacion.v: contiene una implementación funcional de nuestro modelo.
- Soundess.v: contiene la prueba de que nuestra implementación cumple lo especificado en el modelo
  abstracto. Nuevamente, la prueba se dividió en sub-lemas por cada acción posible, esta vez con el
  sufijo `IsSound`. Por ejemplo, para la operación `grant`, el archivo correspondiente es
  `GrantIsSound.v`.

### Propiedades

- ModelProperties.v: Agrupa todas las propiedades que fueron probadas sobre el modelo o la
  implementación en un único archivo. Notar que no todas las pruebas están desarrolladas dentro de
  este módulo, habiéndose extraído las mismas para mantener archivos más chicos y separados.
  Ejemplos de esto son los módulos: `RvkAndNotGrant.v`, `IfPermThenGranted.v` o
  `IfOldAppRunThenVerified.v`.

Solo dos propiedades quedaron por fuera de `ModelProperties.v` y son las siguientes:

- Eavesdropping.v
- IntentSpoofing.v

El resto de los archivos que no fueron mencionados aquí contienen lemas o métodos auxiliares, como
por ejemplo:

- PropertiesAuxFuns.v
- SameEnvLemmas.v
- TraceRelatedLemmas.v
