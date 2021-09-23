using System.Collections;
using System.Collections.Generic;
using UnityEngine;

public class CarBooster : MonoBehaviour
{
    public int boostAmount = 7;
    // Start is called before the first frame update
    void Start()
    {
        GetComponent<Rigidbody>().velocity = new Vector3(0, 0, boostAmount);
    }

    // Update is called once per frame
    void Update()
    {
        
    }
}
