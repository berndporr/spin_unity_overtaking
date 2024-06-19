# Final MSci project by Daumantas Pagojus

## Prerequisites
To run this project you have to install Unity 2019.4.13: https://unity3d.com/get-unity/download/archive (I have not tested the project on newer versions)
You will also need to install Spin model checker (http://spinroot.com/spin/Man/README.html) and add it to the Path, so that it could be reached using command "spin" from the command prompt/terminal. This is how Simulator invokes the model checking part.

## Promela Models
Promela models used can be found in the home directory of the repository. There are 4 types of files:
* The Never Claim which is used by all models (nc_overtake.pml)
* Files to play with through terminal - oncoming_3.pml (the Final Model), oncoming_1.pml, no_oncoming_1.pml, no_oncoming_3.pml
* Template files which are used by the Simulator - they contain placeholders which are replaced with sensor values every time the model checking is done. These files are oncoming_3_template.pml and preparations_template.pml.
* Generated files that are used by the Simulator - these are template files where placeholders have been replaced with actual values from the simulator. These are the files that the Simulator verifies using Spin to get a list of Actions to do. These files are generated_oncoming_3.pml and generated_preparations.pml.

## Launching the Simulator
To launch the project in Unity navigate to "AI car Simulator/Assets/Scenes" and open AutoTraffic Unity scene using Unity.
When the project opens, you should see a Scene with only the Autonomous Vehicle in it.

To start the simmulation press the > icon at the middle top of the screen. Left and Right lane vehicle then should spawn and the Autonomous Vehicle should start moving. Pressing > again will Stop the simulation.
What the autonomous vehicle is doing can be seen in the console window where major events are logged.

Simulator can be paused/unpaused using the || Button.

After running the simulator, all Promela models that have been used will be stored in the ~/logs folder for analysing what went wrong.

NOTE: I have only tested the Simulator on Windows 10. While I do not see why it should not run on other platforms, I give no guarantees.
