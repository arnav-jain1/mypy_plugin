# https://stackoverflow.com/questions/57534072/how-to-fix-runtimeerror-size-mismatch-in-pytorch

import torch
import torch.nn as nn
import torch.nn.functional as F

import torch.optim as optim

import torchvision
import torchvision.transforms as transforms


class Net(nn.Module):
    def __init__(self):
        super(Net, self).__init__()
        self.conv1 = nn.Conv2d(3, 200, 5)
        self.pool = nn.MaxPool2d(2, 2)
        self.conv2 = nn.Conv2d(200, 180, 5)
        self.fc1 = nn.Linear(2092500, 120)
        self.fc2 = nn.Linear(120, 84)
        self.fc3 = nn.Linear(84,5)     

    def forward(self, x):
        x = self.pool(F.relu(self.conv1(x)))
        x = self.pool(F.relu(self.conv2(x)))
        x = x.view(x.shape[0], -1)
        x = F.relu(self.fc1(x))
        x = F.relu(self.fc2(x))
        x = self.fc3(x)
        return x


def load_dataset():
    data_path = '../../../data/COCO'

    transform = transforms.Compose(
                [transforms.Resize((512,384)),
                    transforms.ToTensor(),
                    transforms.Normalize((0.5, 0.5, 0.5), (0.5, 0.5, 0.5))])


    train_dataset = torchvision.datasets.ImageFolder(root=data_path,transform=transform)
    train_loader = torch.utils.data.DataLoader(train_dataset,batch_size=7,num_workers=0,shuffle=True)

    return train_loader



################# <FOR EXPERIMENT: CUSTOM TRAINING LOOP>
epochs = 1
device = "cuda"
lr = 0.1

train_loader = load_dataset()

model = Net().to(device)
optimizer = optim.Adam(model.parameters(), lr=lr)
loss_function = nn.NLLLoss()

for epoch in range(1, epochs + 1):
    model.train()
    train_loss = 0
    for batch_idx, (data, target) in enumerate(train_loader):
        data = data.to(device)
        target = target.to(device)
        optimizer.zero_grad()
        out = model(data)
        loss = loss_function(out, target)
        loss.backward()
        train_loss += loss.item()

        print("epoch {}/{}, batch={}".format(epoch, epochs, batch_idx))
    optimizer.step()
#################