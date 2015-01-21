module Modules.Imports where

module X where
  module ImportExample where
    data Bool : Set where
      false true : Bool

  x = ImportExample.true

module X′ where
  import ImportExample

  x = ImportExample.true

module X″ where
  import Modules.ImportExample

  x = Modules.ImportExample.true

module X‴ where
  import Modules.ImportExample as ImportExample

  x = ImportExample.true


