import System

printOne : (v : String) -> IO ()
printOne v = do
  env <- System.getEnv v
  putStrLn $ v ++ ":" ++ (fromMaybe "Not found" env)

main : IO ()
main = do
  sequence_ $ map (\v => printOne v)  [ "_HANDLER", "LAMBDA_TASK_ROOT", "AWS_LAMBDA_RUNTIME_API" ]
