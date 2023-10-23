{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
module Lib
    ( startApp
    , app
    ) where

import Data.Aeson
import Data.Aeson.TH
import Network.Wai
import Network.Wai.Handler.Warp
import Servant
import Extracted(exported_get_artist, exported_get_album_and_artist)
-- Note that after extraction, the extracted file must have the following imports added
-- import Data.Char
-- import Data.Bits

-- data User = User
--   { userId        :: Int
--   , userFirstName :: String
--   , userLastName  :: String
--   } deriving (Eq, Show)
-- 
-- $(deriveJSON defaultOptions ''User)

type API = "get_artist_less_than" :> Capture "n" Integer :> Get '[JSON] String
           :<|> "get_album_and_artist" :> Capture "n" Integer :> Get '[JSON] String

startApp :: IO ()
startApp = do putStrLn "Starting server on port 8080"
              run 8080 app

app :: Application
app = serve api server

api :: Proxy API
api = Proxy

server :: Server API
server = get_artist :<|> get_album_and_artist
  where get_artist :: Integer -> Handler String
        get_artist x = return $ exported_get_artist x

        get_album_and_artist :: Integer -> Handler String
        get_album_and_artist x = return $ exported_get_album_and_artist x

