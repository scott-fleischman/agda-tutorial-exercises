module Modules.Advanced where

open import Data.Nat

module X where
  x₁ = 10

  module Y where
    y₁ = 11

    module Z where
      z = 12

    y₂ = 13

  x₂ = 14

module X′ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

  x₂ = suc Y.y₂
  x₂′ = suc (suc Y.Z.z)

module X″ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

    open Z

    y₂′ = suc z
    y₂″ = suc (suc Z.z)

  x₂ = suc Y.y₂
  -- x₂′ = suc (suc Y.z)
  
module X‴ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

    open Z public

    y₂′ = suc z

  x₂ = suc Y.y₂
  x₂′ = suc (suc Y.z)

module X⁗ where
  x₁ = 10

  module Y where
    private
      y₁ = suc x₁

    module Z where
      z = suc y₁

    y₂ = suc Z.z

  x₂ = suc Y.y₂
  -- x₂′ = suc (suc (suc Y.y₁))

module X⁵ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      z′ = z
      z″ = z

    open Z using (z′; z″)

    y₂ = suc z′
    -- y₂′ = suc z

  x₂ = suc Y.y₂

module X⁶ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      z′ = z
      z″ = z

    open Z hiding (z)

    y₂ = suc z′
    -- y₂′ = suc z

  x₂ = suc Y.y₂
  
module X⁷ where
  x₁ = 10

  module Y where
    y₁ = suc x₁

    module Z where
      z = suc y₁
      z′ = z
      z″ = z

    open Z renaming (z to v; z″ to v″)

    y₂ = suc v
    -- y₂″ = suc z
    y₂′ = suc z′

  x₂ = suc Y.y₂
  
