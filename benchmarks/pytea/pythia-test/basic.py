import tensorflow as tf

i0 = tf.ones((3, 4))  # No Error (Correct)
i1 = tf.ones((3, 5))  # One Error (Correct)
i2 = tf.ones((3, 5 % 2))  # No Error (False Negative)
i3 = tf.ones((3, 5))[0]  # No Error (False Negative)
i4 = tf.ones((3, 5))[0:1]  # No Error (False Negative)

a = 1
b = 1
if a == 1:
    b = 4
i5 = tf.ones((3, b))  # One Error (False Positive)

target = tf.ones((4, 10))

with tf.Session() as sess:
    p = tf.matmul(i4, target)
    sess.run(p)
