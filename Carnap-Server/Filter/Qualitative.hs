module Filter.Qualitative (makeQualitativeProblems) where

import Carnap.GHCJS.SharedFunctions (simpleHash, simpleCipher)
import Text.Pandoc
import Control.Monad.State (State, get, put)
import Filter.Util (numof, contentOf, intoChunks,formatChunk, unlines', exerciseWrapper, sanitizeHtml)
import Data.Map (fromList, toList, unions)
import qualified Data.Text as T
import Data.Text (Text)
import Prelude

-- The Int state is the same per-document counter used for proof boxes: it
-- gives each problem a storage key that stays unique even when problems
-- share a number or prompt.
makeQualitativeProblems :: Block -> State Int Block
makeQualitativeProblems cb@(CodeBlock (_,classes,extra) contents)
    | "QualitativeProblem" `elem` classes = do chunks <- mapM (activate classes extra) (intoChunks contents)
                                               return $ Div ("",[],[]) chunks
    | otherwise = return cb
makeQualitativeProblems x = return x

activate :: [Text] -> [(Text, Text)] -> Text -> State Int Block
activate cls extra chunk = do n <- get
                              put (n + 1)
                              return (activate' n cls extra chunk)

activate' :: Int -> [Text] -> [(Text, Text)] -> Text -> Block
activate' n cls extra chunk
    | "MultipleChoice" `elem` cls = mctemplate (opts [("qualitativetype","multiplechoice"), ("goal", safeContentOf h) ])
    | "MultipleSelection" `elem` cls = mctemplate (opts [("qualitativetype","multipleselection"), ("goal", safeContentOf h) ])
    | "ShortAnswer" `elem` cls = template (opts [("qualitativetype", "shortanswer"), ("goal", safeContentOf h) ])
    | "Numerical" `elem` cls = case T.splitOn ":" (safeContentOf h) of
                                   [g,p] -> template (opts [ ("qualitativetype","numerical")
                                                            , ("goal", T.pack $ show (simpleCipher $ T.unpack g))
                                                            , ("problem", sanitizeHtml p)
                                                            ])
                                   _ -> Div ("",[],[]) [Plain [Str "problem with numerical qualitative problem specification"]]
    | otherwise = RawBlock "html" "<div>No Matching Qualitative Problem Type</div>"
    where safeContentOf = sanitizeHtml . contentOf
          (h:t) = formatChunk chunk
          opts adhoc = unions [fromList extra, fromList fixed, fromList adhoc]
          fixed = [ ("type","qualitative")
                  , ("submission", T.concat ["saveAs:", numof h])
                  , ("storage-key", T.concat [numof h, "-", T.pack (show n)])
                  ]
          mctemplate myOpts = exerciseWrapper (toList myOpts) (numof h) $
                              --Need rawblock here to get the linebreaks
                              --right.
                              RawBlock "html" $ T.concat
                              ["<div", optString myOpts, ">"
                               , unlines' (map (T.pack . show . withHash . T.unpack) t)
                               , "</div>"]
          template myOpts = exerciseWrapper (toList myOpts) (numof h) $
                              --Need rawblock here to get the linebreaks
                              --right.
                              RawBlock "html" $ T.concat [ "<div", optString myOpts, ">", unlines' t, "</div>" ]
          optString myOpts = T.concat $ map (\(x,y) -> T.concat [" data-carnap-", x, "=\"", y, "\""]) (toList myOpts)
          withHash s | length s' > 0 = if head s' `elem` ['*','+','-'] then (simpleHash s', tail s') else (simpleHash s',s')
                     | otherwise = (simpleHash s', s')
            where s' = (dropWhile (== ' ') s)
