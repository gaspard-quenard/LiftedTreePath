

<div align="center">
  <video src="https://user-images.githubusercontent.com/99724660/221192291-7e2dc4ec-92d8-4d29-83a2-3f787c1c4eef.mp4" />
</div>
<p align="center">
  <img src="https://user-images.githubusercontent.com/99724660/221203036-fcce9951-4522-4d1c-aaf8-d2775b0368d2.gif" alt="animated" />
</p>

---

# General workflow
  ![logic](https://user-images.githubusercontent.com/99724660/221208016-01a6a56d-a786-46f0-bd95-476eb04e39b5.png)

# Additional info

1. Benchmarks are already available in the project. Use ONLY them
2. The planner takes 3 arguments - [SOLVER] [DOMAIN] [PROBLEM]

# TODO
1. Add preprocessing from SMT (JAVA side)
2. Identify and implement necessary Constraint data structures and Constraint.toString() functions
3. Use Constraints to encode TreeRex rules

# Build

```bash
./gradlew build
```

# Run 

```bash
./gradlew run --args="-d <domain_file> -p <problem_file>"
```