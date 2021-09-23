using System.Collections;
using System.Collections.Generic;
using UnityEngine;

public class CubeController : MonoBehaviour
{
    public Transform car;
    public int x_pos = 0;
    public int lane = 0;
    int laneWidth = 4;
    // Start is called before the first frame update
    void Start()
    {
        this.transform.position = new Vector3(x_pos, car.position.y, car.position.z + 7);
    }

    // Update is called once per frame
    void Update()
    {
        this.transform.position = new Vector3(transform.position.x, car.position.y, car.position.z + 7);
    }

    public void SetLane(int lane)
    {
        this.lane = lane;
        x_pos = laneWidth * lane;
        StartCoroutine(AnimateLaneChange(this.transform, 2f));
    }

    private IEnumerator AnimateLaneChange(Transform target, float dur)
    {
        float t = 0f;
        Vector3 start = target.position;
        while (t < dur)
        {
            target.position = new Vector3(Mathf.Lerp(start.x, x_pos, t / dur), car.position.y, car.position.z + 7);
            yield return null;
            t += Time.deltaTime;
        }
    }
}
