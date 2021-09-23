using System.Collections;
using System.Collections.Generic;
using UnityEngine;

[RequireComponent(typeof(InputManager))]
public class CarController : MonoBehaviour
{
    public InputManager input;
    public List<WheelCollider> throttleWheels;
    public List<WheelCollider> steeringWheels;
    public float strengthCoefficient = 30000f;
    public float maxTurn = 20f;
    // Start is called before the first frame update
    void Start()
    {
        input = GetComponent<InputManager>();
    }

    void FixedUpdate()
    {
        foreach (WheelCollider wheel in throttleWheels) {
            wheel.motorTorque = strengthCoefficient * Time.deltaTime * input.throttle;
            wheel.brakeTorque = strengthCoefficient * Time.deltaTime * input.brake;
        }

        foreach (WheelCollider wheel in steeringWheels)
        {
            //wheel.steerAngle = maxTurn * input.steer;
            wheel.steerAngle = input.steer;

        }
    }
}
