{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      :  KZC.Derive
-- Copyright   :  (c) 2015 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@cs.drexel.edu

module KZC.Derive (
    deriveM,
    deriveBinary,
    deriveLocated
  ) where

import Data.Generics
import Data.Loc
import Data.Symbol
import Text.PrettyPrint.Mainland as PP

deriveM :: (a -> Doc) -> a -> IO ()
deriveM derive (_ :: a) = do
    putDoc $ derive (undefined :: a)
    putStrLn ""

deriveBinary :: forall a . (Typeable a, Data a) => a -> Doc
deriveBinary _ =
    nest 2 $
    text "instance" <+> ctx <> text "Binary" <+> inst <+> text "where" </>
    stack (map putDef constrs) </> getDefs
  where
    (typeName, typeChildren) = splitTyConApp (typeOf (undefined::a))
    nTypeChildren = length typeChildren
    typeLetters = take nTypeChildren allLetters
    allLetters = [char c | c <- ['a'..'z']]

    ctx :: Doc
    ctx | nTypeChildren > 0 = commasep ([text "Binary" <+> a | a <- typeLetters]) <+> text "=>" <> space
        | otherwise         = PP.empty

    inst :: Doc
    inst = parensIf (nTypeChildren > 0) $
           sep (text (tyConName typeName) : typeLetters)

    constrs :: [(Int, String, Int)]
    constrs = map gen $ zip [0..] $ dataTypeConstrs (dataTypeOf (undefined::a))
      where
        gen :: (Int, Constr) -> (Int, String, Int)
        gen (i, con) =
            ( i
            , showConstr con
            , gmapQl (+) 0 (const 1) (fromConstrB empty' con :: a)
            )

    putDef :: (Int, String, Int) -> Doc
    putDef (n, name, ps) =
        nest 2 $
        text "put" <+> wrap pattern <+> text "=" <+/>
        sep ([text "putWord8" <+> ppr n | length constrs >  1] ++
             [text ">>"                 | length constrs >  1 && ps >  0] ++
             [text "return ()"          | length constrs == 1 && ps == 0]) <+>
        folddoc ppSeq (map (text "put" <+>) (take ps allLetters))
      where
        wrap | ps /= 0   = parens
             | otherwise = id

        pattern = spread (text name : take ps allLetters)

        ppSeq x y = x <+> text ">>" <+> y

    getDefs :: Doc
    getDefs | length constrs > 1 =
        nest 2 $
        text "get" <+> text "=" <+> text "do" </>
        text "tag_ <- getWord8" </>
        nest 2 (text "case tag_ of" </>
                stack (map getDef constrs) </>
                text "_" <+> text "->" <+> text "fail" <+> text ("\"" ++ tyConName typeName ++ ": no decoding\"")
               )
            | otherwise =
        text "get" <+> text "=" <+> sep (map getDef constrs)

    getDef :: (Int, String, Int) -> Doc
    getDef (n, name, ps) =
        sep $
        [ppr n <+> text "->" | length constrs > 1] ++
        if ps == 0
           then [text "pure" <+> text name]
           else [text name <+> text "<$>" <+> folddoc ppSeq (replicate ps (text "get"))]
      where
        ppSeq x y = x <+> text "<*>" <+> y

deriveLocated :: forall a . (Typeable a, Data a) => a -> Doc
deriveLocated _ =
    nest 2 $
    text "instance" <+>  text "Located" <+> text (tyConName typeName) <+> text "where" </>
    stack (map locDef constrs)
  where
    (typeName, _) = splitTyConApp (typeOf (undefined::a))
    allLetters = [char c | c <- ['a'..'z']]

    constrs :: [(String, Int)]
    constrs = map gen $ dataTypeConstrs (dataTypeOf (undefined::a))
      where
        gen :: Constr -> (String, Int)
        gen con =
            ( showConstr con
            , gmapQl (+) 0 (const 1) (fromConstrB empty' con :: a)
            )

    locDef :: (String, Int) -> Doc
    locDef (name, ps) =
        nest 2 $
        text "locOf" <+> wrap pattern <+> text "=" <+/>
        case take ps allLetters of
          [] -> error $ "Cannot drive Located: " ++ name
          _  -> text "locOf" <+> char 'l'
      where
        wrap | ps /= 0   = parens
             | otherwise = id

        wilds = replicate (ps - 1) (char '_')

        pattern = spread (text name : wilds ++ [char 'l'])

empty' :: forall a. Data a => a
empty' = Data.Generics.empty
  `extB` pos
  `extB` loc
  `extB` srcloc
  `extB` symbol
  where
    pos :: Pos
    pos = Pos "" 1 1 1

    loc :: Loc
    loc = NoLoc

    srcloc :: SrcLoc
    srcloc = SrcLoc NoLoc

    symbol :: Symbol
    symbol = intern ""
