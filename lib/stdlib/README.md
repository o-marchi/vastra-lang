# Standard library modules

Each `NAME.vas` here is the module `NAME`, embedded in the `vastra` binary
(see `lib/embed`). A program uses one with `(:require [NAME :as alias])`.
The core (`string/`, `option/`, `result/`, `dict/` and the rest of
`lib/prelude.vas`) needs no require.
