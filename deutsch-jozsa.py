n = 3

# create a quantum circuit with 4 qubits and 3 classical bits
from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister, transpile
qr = QuantumRegister(n + 1) 
cr = ClassicalRegister(n)
qc = QuantumCircuit(qr, cr)

# apply a hadamard gate to each qubit
for i in range(n): qc.h(qr[i])
qc.barrier()

# flip the last qubit and apply hadamard
qc.x(qr[n])
qc.h(qr[n])

# define the oracle gate as a constant function - flip nth qubit
qc.barrier()
qc.x(qr[n])

# gates and measure
qc.barrier()
for i in range(n): 
    qc.h(i)
    qc.measure(qr[i], cr[i])

# draw the resulting circuit
import matplotlib.pyplot as plt
qc.draw('mpl') 
plt.show()

# simulate the circuit
from qiskit_aer import AerSimulator
sim = AerSimulator()
result = sim.run(transpile(qc, sim)).result()

# plot the results
from qiskit.visualization import plot_histogram
counts = result.get_counts(qc)
plot_histogram(counts, title='Bell-State counts')
plt.show()