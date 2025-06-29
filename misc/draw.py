
import matplotlib.pyplot as plt
import numpy as np

# Read data from files
def read_data(filename):
    with open(filename, 'r') as file:
        return [float(line.strip()) for line in file.readlines()]

data_a = read_data('a.txt')
data_b = read_data('b.txt')
data_c = read_data('c.txt')

# Compute averages
avg_a = sum(data_a) / len(data_a)
avg_b = sum(data_b) / len(data_b)
avg_c = sum(data_c) / len(data_c)

print(f"Average time - A: {avg_a:.6f}s, B: {avg_b:.6f}s, C: {avg_c:.6f}s")

# Create histogram bins
bins = np.linspace(min(min(data_a), min(data_b), min(data_c)),
                   max(max(data_a), max(data_b), max(data_c))/3, 30)

# Compute histograms
hist_a, _ = np.histogram(data_a, bins=bins)
hist_b, _ = np.histogram(data_b, bins=bins)
hist_c, _ = np.histogram(data_c, bins=bins)

# Width of each bar and positions
width = (bins[1] - bins[0]) / 4
bin_centers = bins[:-1] + width

# Plot histograms with dodged bars
plt.bar(bin_centers - width, hist_a, width=width, label='Preserve', align='center')
plt.bar(bin_centers, hist_b, width=width, label='Node Deletion', align='center')
plt.bar(bin_centers + width, hist_c, width=width, label='Forwarding Path Change', align='center')

# Labeling and layout
plt.xlabel('Time (Seconds)')
plt.ylabel('Frequency')
plt.title('Relational NetKAT Time Comparison on 2000 datas')
plt.legend()
plt.tight_layout()

# Save figure
plt.savefig('dodged_histogram_comparison.png')
plt.show()

