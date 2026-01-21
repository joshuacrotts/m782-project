module Values where

open import Terms

data NatVal : Term → Set where
    --
    -- ---------------------
    --      zero nval
    nv-zero : NatVal zero

    --       v nval
    -- ---------------------
    --     suc v nval
    nv-suc : ∀ {v} → NatVal v → NatVal (suc v)


data Val : Term → Set where

    --
    -- ---------------------
    --      true val
    v-true : Val true

    --
    -- ---------------------
    --      false val
    v-false : Val false

    --      v nval
    -- ---------------------
    --      v val
    v-val : ∀ {v} → NatVal v → Val v

