using System.Collections;
using System.Collections.Generic;
using UnityEngine;

public class AutoTraffic : MonoBehaviour
{
    public Transform AICar;
    private Vector3 leftLaneSpawnPosition;
    private Vector3 rightLaneSpawnPosition;
    public GameObject leftCarPrefab;
    public GameObject rightCarPrefab;
    private int segmentSize = 21;
    private Vector3 lastLeftSpawnPos;
    private Vector3 lastRightSpawnPos;
    private int laneWidth = 4;
    private int numLeftCars = 60;
    private int numRightCars = 5;
    private int num_spawned_cars = 0;
    private int passedCars = 0;
    private int numFirstConsequentChoices = 0;

    int[] leftPositions = new int[] { 1, 2, 3, 4 };
    List<GameObject> leftCars = new List<GameObject>();

    int[] rightPositions = new int[] { 8, 12, 12, 16, 16, 20, 20, 20 };
    List<GameObject> rightCars = new List<GameObject>();

    void Start()
    {
        lastLeftSpawnPos = AICar.position + new Vector3(0,0,2 + 0.5f * segmentSize);
        lastRightSpawnPos = AICar.position + new Vector3(laneWidth, 0, 2 + 2.5f * segmentSize);

    }


    void Update()
    {
        // Spawn left cars
        while (leftCars.Count < numLeftCars)
        {
            // Don't spawn too many consequent cars on left lane so that we would be able to pass.
            int randomLeftPosition;
            while (true) {
                randomLeftPosition = leftPositions[Random.Range(0, leftPositions.Length)];
                print($"random left: {randomLeftPosition}");
                if (randomLeftPosition == 1)
                {
                    numFirstConsequentChoices++;
                }
                else {
                    numFirstConsequentChoices = 0;
                }

                if (numFirstConsequentChoices < 2) {
                    print("break");
                    break;
                }
                print($"numFirstConsequent: {numFirstConsequentChoices}");
            }
            
            lastLeftSpawnPos += new Vector3(0, 0, segmentSize) * randomLeftPosition;
            GameObject car = Instantiate(leftCarPrefab, lastLeftSpawnPos, Quaternion.Euler(0, 0, 0));
            car.name = $"bot_{num_spawned_cars}";
            num_spawned_cars++;
            car.GetComponent<Rigidbody>().velocity = new Vector3(0, 0, 7);
            leftCars.Add(car);
        }
        // Spawn Right cars
        while (rightCars.Count < numRightCars)
        {
            lastRightSpawnPos += new Vector3(0, 0, segmentSize) * rightPositions[Random.Range(0, rightPositions.Length)];
            GameObject car = Instantiate(rightCarPrefab, lastRightSpawnPos, Quaternion.Euler(0, 180, 0));
            car.name = $"bot_{num_spawned_cars}";
            num_spawned_cars++;
            car.GetComponent<Rigidbody>().velocity = new Vector3(0, 0, -7);
            rightCars.Add(car);
        }

        // Destroy passed cars
        GameObject firstCar = leftCars[0];
        if (AICar.position.z - firstCar.transform.position.z > 10 * segmentSize) {
            leftCars.Remove(firstCar);
            Destroy(firstCar);

            // Update spawn pos to the furthest car in the lane, to avoid spawning behind us.
            lastLeftSpawnPos = leftCars[leftCars.Count - 1].transform.position;
            passedCars++;
            print($"Passed cars~: {passedCars}");
            
        }
        firstCar = rightCars[0];
        if (AICar.position.z - firstCar.transform.position.z > 10 * segmentSize)
        {
            rightCars.Remove(firstCar);
            Destroy(firstCar);
            // Update spawn pos to the furthest car in the lane, to avoid spawning behind us.
            lastRightSpawnPos = rightCars[rightCars.Count - 1].transform.position;
        }
    }
}
