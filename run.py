import os
import subprocess

base_dir = "/data/OpenAgentBenchmarks/"
sinks_dir = "/root/PyCG/sink_files"
output_base_dir = "/root/result"

os.makedirs(output_base_dir, exist_ok=True)

projects = [name for name in os.listdir(base_dir) if os.path.isdir(os.path.join(base_dir, name))]

sinks_files = [os.path.join(sinks_dir, f) for f in os.listdir(sinks_dir) if os.path.isfile(os.path.join(sinks_dir, f))]

for project in projects:
    project_path = os.path.join(base_dir, project)
    project_output_dir = os.path.join(output_base_dir, project)
    os.makedirs(project_output_dir, exist_ok=True)

    print(f"🔍 Processing project: {project}")

    for sinks_file in sinks_files:
        sinks_name = os.path.basename(sinks_file).replace(".txt", "")

        output_json = os.path.join(project_output_dir, f"{sinks_name}.json")
        log_file = os.path.join(project_output_dir, f"{sinks_name}.log")

        command = [
            "/root/anaconda3/bin/python", "-m", "pycg",
            "--package", project_path,
            "--output", output_json,
            "--sinks", sinks_file,
            "--max-iter", "33"
        ]

        print(f"  ➡ Running with sinks: {sinks_name}")

        with open(log_file, "w") as log:
            try:
                print(' '.join(command))
                result = subprocess.run(command, stdout=log, stderr=log, text=True)

                if result.returncode == 0:
                    print(f"  ✅ Successfully processed {project} with {sinks_name}, results saved to {output_json}")
                else:
                    print(f"  ❌ Failed processing {project} with {sinks_name}, check {log_file} for details")

            except Exception as e:
                print(f"  ❌ Error processing {project} with {sinks_name}: {e}")
                log.write(f"Error: {e}\n")
