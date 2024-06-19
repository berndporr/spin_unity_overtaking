using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using System.Threading;
using System.IO;

public class CarStateController : MonoBehaviour
{
    public CarActions carActions;
    public bool gamePaused = false;
    public bool doNextState;
    private Thread modelCheckerThread;
    string pmlFile;
    string pmlFilePreparations;
    string pmlScriptsFolder;
    private bool actionsReady = false;
    private Environment env;
    public bool recalculateActions = false;

    public enum CarState
    {
        Drive = 1,
        Accelerate = 2,
        Brake = 3,
        LeftLaneChange = 4,
        RightLaneChange = 5
    }
    Queue<CarState> actions = new Queue<CarState>();


    // Start is called before the first frame update
    void Start()
    {
        UnityEditor.SceneView.FocusWindowIfItsOpen(typeof(UnityEditor.SceneView)); // DEBUG step for focusing on scene view on Play
        doNextState = true;

        pmlFile = "oncoming_3";
        pmlFilePreparations = "preparations";

        pmlScriptsFolder = Path.Combine(Application.dataPath, "../../"); // model checker files

        try {
            Directory.Delete($"{pmlScriptsFolder}/logs/{pmlFile}", true);
        } catch(DirectoryNotFoundException e) { }

        try
        {
            Directory.Delete($"{pmlScriptsFolder}/logs/{pmlFilePreparations}", true);
        }
        catch (DirectoryNotFoundException e) { }


        Directory.CreateDirectory($"{pmlScriptsFolder}/logs/{pmlFile}");
        Directory.CreateDirectory($"{pmlScriptsFolder}/logs/{pmlFilePreparations}");


    }

    // Update is called once per frame
    void Update()
    {

        if (Input.GetKeyDown(KeyCode.P))
        {
            if (gamePaused)
            {
                ResumeGame();
            }
            else
            {
                PauseGame();
            }
        }

        // When thread completes generating actions, resume the game
        if (actionsReady) {
            ResumeGame();
            actionsReady = false;
        }

        if (doNextState && recalculateActions)
        {
            PauseGame();
            recalculateActions = false;
            env = GetComponent<Sensors>().env;
            modelCheckerThread = new Thread(RunModelChecker);
            modelCheckerThread.Start();
        }

        if (doNextState)
        {

            env = GetComponent<Sensors>().env;
            //printState();

            if (actions.Count == 0)
            {
                if (env.isObsFront()) {
                    print("Recalc: Car in front, but we don't have actions");
                    recalculateActions = true;
                }
            } else
            {
                CarState action = actions.Dequeue();
                switch (action)
                {
                    case CarState.Accelerate:
                        doNextState = false;
                        carActions.Accelerate();
                        break;
                    case CarState.Brake:
                        doNextState = false;
                        carActions.Brake();
                        break;
                    case CarState.Drive:
                        doNextState = false;
                        carActions.Drive();
                        break;
                    case CarState.LeftLaneChange:
                        doNextState = false;
                        carActions.LeftLaneChange();
                        break;
                    case CarState.RightLaneChange:
                        doNextState = false;
                        carActions.RightLaneChange();
                        break;
                }
            }
        }
    }

    void RunModelChecker() {
        print("Model Checker Start");
        File.Delete($"{pmlScriptsFolder}/generated_{pmlFile}.pml.trail");
        UpdateModelFile(env, pmlFile);
        System.Diagnostics.ProcessStartInfo runModelCheckerProcessInfo = new System.Diagnostics.ProcessStartInfo("spin")
        {
            UseShellExecute = false,
            WorkingDirectory = pmlScriptsFolder,
            CreateNoWindow = true,
            Arguments = $"-B -o1 -o2 -o3 -o4 -o5 -search generated_{pmlFile}.pml"
        };
        System.Diagnostics.Process.Start(runModelCheckerProcessInfo).WaitForExit();

        System.Diagnostics.ProcessStartInfo runAnalysingProcessInfo = new System.Diagnostics.ProcessStartInfo("spin")
        {
            UseShellExecute = false,
            WorkingDirectory = pmlScriptsFolder,
            CreateNoWindow = true,
            Arguments = $"-t generated_{pmlFile}.pml",
            RedirectStandardOutput = true
    };
        System.Diagnostics.Process runModelCheckerProcess = System.Diagnostics.Process.Start(runAnalysingProcessInfo);
        
        runModelCheckerProcess.WaitForExit();


        StreamReader solutionReader = runModelCheckerProcess.StandardOutput;
        
        actions = GenerateActions(solutionReader);

        if (actions.Count == 0)
        {
            actions = RunPreparationsChecker();
            if (actions.Count == 0) {
                print("Failed to find a path");
                PauseGame();
            }
        }

        actionsReady = true;
        solutionReader.Dispose();
    }

    Queue<CarState> RunPreparationsChecker() {
        print("Preparations Checker Start");
        File.Delete($"{pmlScriptsFolder}/generated_{pmlFilePreparations}.pml.trail");
        UpdateModelFile(env, pmlFilePreparations);
        System.Diagnostics.ProcessStartInfo runModelCheckerProcessInfo = new System.Diagnostics.ProcessStartInfo("spin")
        {
            UseShellExecute = false,
            WorkingDirectory = pmlScriptsFolder,
            CreateNoWindow = true,
            Arguments = $"-B -o1 -o2 -o3 -o4 -o5 -search generated_{pmlFilePreparations}.pml"
        };
        System.Diagnostics.Process.Start(runModelCheckerProcessInfo).WaitForExit();

        System.Diagnostics.ProcessStartInfo runAnalysingProcessInfo = new System.Diagnostics.ProcessStartInfo("spin")
        {
            UseShellExecute = false,
            WorkingDirectory = pmlScriptsFolder,
            CreateNoWindow = true,
            Arguments = $"-t generated_{pmlFilePreparations}.pml",
            RedirectStandardOutput = true
        };
        System.Diagnostics.Process runModelCheckerProcess = System.Diagnostics.Process.Start(runAnalysingProcessInfo);

        runModelCheckerProcess.WaitForExit();


        StreamReader solutionReader = runModelCheckerProcess.StandardOutput;

        return GenerateActions(solutionReader);
    }


    Queue<CarState> GenerateActions(StreamReader solutionReader) {
        Queue<CarState> newActions = new Queue<CarState>();
        while (solutionReader.Peek() >= 0)
        {

            string line = solutionReader.ReadLine().Replace("\n", "").Replace(" ", "");
            switch (line)
            {
                case "STATE_accelerate":
                    newActions.Enqueue(CarState.Accelerate);
                    break;
                case "STATE_brake":
                    newActions.Enqueue(CarState.Brake);
                    break;
                case "STATE_left_lane_change":
                    newActions.Enqueue(CarState.LeftLaneChange);
                    break;
                case "STATE_right_lane_change":
                    newActions.Enqueue(CarState.RightLaneChange);
                    break;
                case "STATE_drive":
                    newActions.Enqueue(CarState.Drive);
                    break;
                default:
                    break;
            }
        }
        return newActions;
    }

    void UpdateModelFile(Environment env, string filename) {
        // Read template

        string template = File.ReadAllText($"{pmlScriptsFolder}/{filename}_template.pml");

        // Update values
        template = template.Replace("PLACEHOLDER_OTHER_POSITION", env.GetOtherPosition().ToString());
        template = template.Replace("PLACEHOLDER_ONCOMING_POSITION", env.GetOncomingPosition().ToString());
        template = template.Replace("PLACEHOLDER_NEXT_ONCOMING_POSITION", env.GetNextOncomingPosition().ToString());
        template = template.Replace("PLACEHOLDER_LANE", laneNumToName(env.getLane()));
        template = template.Replace("PLACEHOLDER_AI_POSITION", env.GetAiCarPosition().ToString());
        template = template.Replace("PLACEHOLDER_REAR_POSITION", env.GetRearPosition().ToString());
        template = template.Replace("PLACEHOLDER_OBSTACLES", string.Join(",", env.GetObstaclesPositions().ToArray()));
        template = template.Replace("PLACEHOLDER_NUM_OBSTACLES", env.GetObstaclesPositions().Count.ToString());

        //printState();
        // Write PML file
        File.WriteAllText($"{pmlScriptsFolder}/generated_{filename}.pml", template);
        File.WriteAllText($"{pmlScriptsFolder}/logs/{filename}/generated_{filename}_{System.DateTime.Now.ToString("yyyy-MM-dd_hh-mm-ss")}.pml", template);
    }

    void printState() {
        print($"Observed environment:\n" +
            $"Other position: {env.GetOtherPosition().ToString()}\n" +
            $"Rear position: {env.GetRearPosition().ToString()}\n" +
            $"Next position: {env.GetNextPosition().ToString()}\n" +
            $"Oncoming position: {env.GetOncomingPosition().ToString()}\n" +
            $"Next Oncoming Position: {env.GetNextOncomingPosition().ToString()}\n" +
            $"lane: {laneNumToName(env.getLane())}");
    }



    string laneNumToName(int laneNum) {
        switch (laneNum) {
            case 0:
                return "left";
            case 1:
                return "right";
            default:
                return "left";
        }
    }

    public void PauseGame()
    {
        print("Game Paused");
        Time.timeScale = 0;
        gamePaused = true;
        doNextState = false;
    }

    public void ResumeGame()
    {
        print("Game Resumed");
        Time.timeScale = 1;
        gamePaused = false;
        doNextState = true;
    }


    void DoSnake() {
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.RightLaneChange);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.LeftLaneChange);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.RightLaneChange);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.LeftLaneChange);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.RightLaneChange);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.LeftLaneChange);
    }

    void DoOvertake() {
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.RightLaneChange);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.LeftLaneChange);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
    }

    void AccelStraight() {
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
    }

    void DoOvertakeWithDrive() {
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.RightLaneChange);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.Accelerate);
        actions.Enqueue(CarState.LeftLaneChange);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
        actions.Enqueue(CarState.Drive);
    }
}
