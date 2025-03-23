# https://stackoverflow.com/questions/59108988/flatten-tensor-in-pytorch-convolutional-neural-network-size-mismatch-error

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
from torch.utils.data import DataLoader

x = np.random.rand(1_00, 3, 100, 100)
y = np.random.randint(0, 2, 1_00)

if torch.cuda.is_available():
    x = torch.from_numpy(x.astype('float32')).cuda()
    y = torch.from_numpy(y.astype('float32')).cuda()

class ConvNet(nn.Module):

    def __init__(self):
        super().__init__()
        self.conv1 = nn.Conv2d(3, 32, 3)
        self.conv2 = nn.Conv2d(32, 64, 3)
        self.conv3 = nn.Conv2d(64, 128, 3)

        self.fc1 = nn.Linear(128, 1024) # 128 is wrong here
        self.fc2 = nn.Linear(1024, 1)

    def forward(self, x):
        x = F.max_pool2d(F.relu(self.conv1(x)), (2, 2))
        x = F.max_pool2d(F.relu(self.conv2(x)), (2, 2))
        x = F.max_pool2d(F.relu(self.conv3(x)), (2, 2))
        x = x.view(x.size(0), -1)
        x = F.relu(self.fc1(x))
        x = torch.sigmoid(self.fc2(x))
        return x

net = ConvNet()
net.cuda()
optimizer = optim.Adam(net.parameters(), lr=0.03)
loss_function = nn.BCELoss()

class Train:

    def __init__(self):
        self.len = x.shape[0]
        self.x_train = x
        self.y_train = y

    def __getitem__(self, index):
        return x[index], y[index].unsqueeze(0)

    def __len__(self):
        return self.len

train = Train()
train_loader = DataLoader(dataset=train, batch_size=64, shuffle=True)

epochs = 1
train_losses = list()
for e in range(epochs):
    running_loss = 0
    for images, labels in train_loader:
        optimizer.zero_grad()
        log_ps = net(images)
        loss = loss_function(log_ps, labels)
        loss.backward()
        optimizer.step()
        running_loss += loss.item()
    print('It\'s working.')