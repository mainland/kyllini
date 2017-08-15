instance Located TyVar where
  locOf (TyVar l) = locOf l
instance Located Type where
  locOf (UnitT l) = locOf l
  locOf (BoolT l) = locOf l
  locOf (IntT _ l) = locOf l
  locOf (FixT _ l) = locOf l
  locOf (FloatT _ l) = locOf l
  locOf (StringT l) = locOf l
  locOf (StructT _ _ l) = locOf l
  locOf (SynT _ _ l) = locOf l
  locOf (ArrT _ _ l) = locOf l
  locOf (C _ l) = locOf l
  locOf (T l) = locOf l
  locOf (ST _ _ _ _ l) = locOf l
  locOf (RefT _ l) = locOf l
  locOf (FunT _ _ l) = locOf l
  locOf (NatT _ l) = locOf l
  locOf (UnopT _ _ l) = locOf l
  locOf (BinopT _ _ _ l) = locOf l
  locOf (ForallT _ _ l) = locOf l
  locOf (TyVarT _ l) = locOf l
  locOf (MetaT _ l) = locOf l
instance Located StructDef where
  locOf (StructDef _ _ _ l) = locOf l
  locOf (TypeDef _ _ _ l) = locOf l
