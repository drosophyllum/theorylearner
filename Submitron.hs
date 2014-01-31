 {-# LANGUAGE OverloadedStrings #-}

module Submitron where
import Database.MySQL.Simple
submit:: String -> IO ()
submit datum = do
	conn <- connect defaultConnectInfo { connectHost = "sql.mit.edu",connectUser="spock", connectPassword = "drosophyllum" , connectDatabase = "spock+urop"}
	execute conn"insert into flat (datum) values (?);"  [show datum]
	return () 
