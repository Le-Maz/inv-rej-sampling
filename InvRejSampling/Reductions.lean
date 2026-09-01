import InvRejSampling.Circuit

example : Circuit.cost (Circuit.memSecEncode false 1024 512) = 16936961 := by native_decide
example : Circuit.cost (Circuit.memSecEncode true 1024 512) = 38355969 := by native_decide
example : Circuit.cost (Circuit.memSecEncode false 1280 768) = 40329219 := by native_decide
example : Circuit.cost (Circuit.memSecEncode true 1280 768) = 96675843 := by native_decide
example : Circuit.cost (Circuit.memSecEncode false 1536 1024) = 40335363 := by native_decide
example : Circuit.cost (Circuit.memSecEncode true 1536 1024) = 96681987 := by native_decide
